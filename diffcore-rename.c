/*
 * Copyright (C) 2005 Junio C Hamano
 */
#include "cache.h"
#include "diff.h"
#include "diffcore.h"
#include "hash.h"

#define DEBUG_BULKMOVE 0

#if DEBUG_BULKMOVE
#define debug_bulkmove(args) __debug_bulkmove args
void __debug_bulkmove(const char *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);
	fprintf(stderr, "[DBG] ");
	vfprintf(stderr, fmt, ap);
	va_end(ap);
}
#else
#define debug_bulkmove(args) do { /*nothing */ } while (0)
#endif

/* Table of rename/copy destinations */

static struct diff_rename_dst {
	struct diff_filespec *two;
	struct diff_filepair *pair;
	unsigned i_am_not_single:1; /* does not look for a match, only here to be looked at */
} *rename_dst;
static int rename_dst_nr, rename_dst_alloc;

/*
 * Do a binary search of "two" in "rename_dst", inserting it if not found.
 */
static struct diff_rename_dst *locate_rename_dst(struct diff_filespec *two,
						 int insert_ok)
{
	int first, last;

	first = 0;
	last = rename_dst_nr;
	while (last > first) {
		int next = (last + first) >> 1;
		struct diff_rename_dst *dst = &(rename_dst[next]);
		int cmp = strcmp(two->path, dst->two->path);
		if (!cmp)
			return dst;
		if (cmp < 0) {
			last = next;
			continue;
		}
		first = next+1;
	}
	/* not found */
	if (!insert_ok)
		return NULL;
	/* insert to make it at "first" */
	if (rename_dst_alloc <= rename_dst_nr) {
		rename_dst_alloc = alloc_nr(rename_dst_alloc);
		rename_dst = xrealloc(rename_dst,
				      rename_dst_alloc * sizeof(*rename_dst));
	}
	rename_dst_nr++;
	if (first < rename_dst_nr)
		memmove(rename_dst + first + 1, rename_dst + first,
			(rename_dst_nr - first - 1) * sizeof(*rename_dst));
	rename_dst[first].two = alloc_filespec(two->path);
	fill_filespec(rename_dst[first].two, two->sha1, two->mode);
	rename_dst[first].pair = NULL;
	rename_dst[first].i_am_not_single = 0;
	return &(rename_dst[first]);
}

/*
 * Do a binary search in "rename_dst" of any entry under "dirname".
 */
static struct diff_rename_dst *locate_rename_dst_dir(const char *dirname)
{
	int first, last;
	int prefixlength = strlen(dirname);

	first = 0;
	last = rename_dst_nr;
	while (last > first) {
		int next = (last + first) >> 1;
		struct diff_rename_dst *dst = &(rename_dst[next]);
		int cmp = strncmp(dirname, dst->two->path, prefixlength);
		if (!cmp)
			return dst;
		if (cmp < 0) {
			last = next;
			continue;
		}
		first = next+1;
	}
	/* not found */
	return NULL;
}

/* Table of rename/copy src files */
static struct diff_rename_src {
	struct diff_filespec *one;
	unsigned short score; /* to remember the break score */
} *rename_src;
static int rename_src_nr, rename_src_alloc;

static struct diff_rename_src *register_rename_src(struct diff_filespec *one,
						   unsigned short score)
{
	int first, last;

	first = 0;
	last = rename_src_nr;
	while (last > first) {
		int next = (last + first) >> 1;
		struct diff_rename_src *src = &(rename_src[next]);
		int cmp = strcmp(one->path, src->one->path);
		if (!cmp)
			return src;
		if (cmp < 0) {
			last = next;
			continue;
		}
		first = next+1;
	}

	/* insert to make it at "first" */
	if (rename_src_alloc <= rename_src_nr) {
		rename_src_alloc = alloc_nr(rename_src_alloc);
		rename_src = xrealloc(rename_src,
				      rename_src_alloc * sizeof(*rename_src));
	}
	rename_src_nr++;
	if (first < rename_src_nr)
		memmove(rename_src + first + 1, rename_src + first,
			(rename_src_nr - first - 1) * sizeof(*rename_src));
	rename_src[first].one = one;
	rename_src[first].score = score;
	return &(rename_src[first]);
}

static int basename_same(struct diff_filespec *src, struct diff_filespec *dst)
{
	int src_len = strlen(src->path), dst_len = strlen(dst->path);
	while (src_len && dst_len) {
		char c1 = src->path[--src_len];
		char c2 = dst->path[--dst_len];
		if (c1 != c2)
			return 0;
		if (c1 == '/')
			return 1;
	}
	return (!src_len || src->path[src_len - 1] == '/') &&
		(!dst_len || dst->path[dst_len - 1] == '/');
}

struct diff_score {
	int src; /* index in rename_src */
	int dst; /* index in rename_dst */
	unsigned short score;
	short name_score;
};

static int estimate_similarity(struct diff_filespec *src,
			       struct diff_filespec *dst,
			       int minimum_score)
{
	/* src points at a file that existed in the original tree (or
	 * optionally a file in the destination tree) and dst points
	 * at a newly created file.  They may be quite similar, in which
	 * case we want to say src is renamed to dst or src is copied into
	 * dst, and then some edit has been applied to dst.
	 *
	 * Compare them and return how similar they are, representing
	 * the score as an integer between 0 and MAX_SCORE.
	 *
	 * When there is an exact match, it is considered a better
	 * match than anything else; the destination does not even
	 * call into this function in that case.
	 */
	unsigned long max_size, delta_size, base_size, src_copied, literal_added;
	unsigned long delta_limit;
	int score;

	/* We deal only with regular files.  Symlink renames are handled
	 * only when they are exact matches --- in other words, no edits
	 * after renaming.
	 */
	if (!S_ISREG(src->mode) || !S_ISREG(dst->mode))
		return 0;

	/*
	 * Need to check that source and destination sizes are
	 * filled in before comparing them.
	 *
	 * If we already have "cnt_data" filled in, we know it's
	 * all good (avoid checking the size for zero, as that
	 * is a possible size - we really should have a flag to
	 * say whether the size is valid or not!)
	 */
	if (!src->cnt_data && diff_populate_filespec(src, 1))
		return 0;
	if (!dst->cnt_data && diff_populate_filespec(dst, 1))
		return 0;

	max_size = ((src->size > dst->size) ? src->size : dst->size);
	base_size = ((src->size < dst->size) ? src->size : dst->size);
	delta_size = max_size - base_size;

	/* We would not consider edits that change the file size so
	 * drastically.  delta_size must be smaller than
	 * (MAX_SCORE-minimum_score)/MAX_SCORE * min(src->size, dst->size).
	 *
	 * Note that base_size == 0 case is handled here already
	 * and the final score computation below would not have a
	 * divide-by-zero issue.
	 */
	if (base_size * (MAX_SCORE-minimum_score) < delta_size * MAX_SCORE)
		return 0;

	if (!src->cnt_data && diff_populate_filespec(src, 0))
		return 0;
	if (!dst->cnt_data && diff_populate_filespec(dst, 0))
		return 0;

	delta_limit = (unsigned long)
		(base_size * (MAX_SCORE-minimum_score) / MAX_SCORE);
	if (diffcore_count_changes(src, dst,
				   &src->cnt_data, &dst->cnt_data,
				   delta_limit,
				   &src_copied, &literal_added))
		return 0;

	/* How similar are they?
	 * what percentage of material in dst are from source?
	 */
	if (!dst->size)
		score = 0; /* should not happen */
	else
		score = (int)(src_copied * MAX_SCORE / max_size);
	return score;
}

static void record_rename_pair(int dst_index, int src_index, int score)
{
	struct diff_filespec *src, *dst;
	struct diff_filepair *dp;

	if (rename_dst[dst_index].pair)
		die("internal error: dst already matched.");

	src = rename_src[src_index].one;
	src->rename_used++;
	src->count++;

	dst = rename_dst[dst_index].two;
	dst->count++;

	dp = diff_queue(NULL, src, dst);
	dp->renamed_pair = 1;
	if (!strcmp(src->path, dst->path))
		dp->score = rename_src[src_index].score;
	else
		dp->score = score;
	rename_dst[dst_index].pair = dp;
}

/*
 * We sort the rename similarity matrix with the score, in descending
 * order (the most similar first).
 */
static int score_compare(const void *a_, const void *b_)
{
	const struct diff_score *a = a_, *b = b_;

	/* sink the unused ones to the bottom */
	if (a->dst < 0)
		return (0 <= b->dst);
	else if (b->dst < 0)
		return -1;

	if (a->score == b->score)
		return b->name_score - a->name_score;

	return b->score - a->score;
}

struct file_similarity {
	int src_dst, index;
	struct diff_filespec *filespec;
	struct file_similarity *next;
};

static int find_identical_files(struct file_similarity *src,
				struct file_similarity *dst)
{
	int renames = 0;

	/*
	 * Walk over all the destinations ...
	 */
	do {
		struct diff_filespec *target = dst->filespec;
		struct file_similarity *p, *best;
		int i = 100, best_score = -1;

		/*
		 * .. to find the best source match
		 */
		best = NULL;
		for (p = src; p; p = p->next) {
			int score;
			struct diff_filespec *source = p->filespec;

			/* False hash collision? */
			if (hashcmp(source->sha1, target->sha1))
				continue;
			/* Non-regular files? If so, the modes must match! */
			if (!S_ISREG(source->mode) || !S_ISREG(target->mode)) {
				if (source->mode != target->mode)
					continue;
			}
			/* Give higher scores to sources that haven't been used already */
			score = !source->rename_used;
			score += basename_same(source, target);
			if (score > best_score) {
				best = p;
				best_score = score;
				if (score == 2)
					break;
			}

			/* Too many identical alternatives? Pick one */
			if (!--i)
				break;
		}
		if (best) {
			record_rename_pair(dst->index, best->index, MAX_SCORE);
			renames++;
		}
	} while ((dst = dst->next) != NULL);
	return renames;
}

static void free_similarity_list(struct file_similarity *p)
{
	while (p) {
		struct file_similarity *entry = p;
		p = p->next;
		free(entry);
	}
}

static int find_same_files(void *ptr)
{
	int ret;
	struct file_similarity *p = ptr;
	struct file_similarity *src = NULL, *dst = NULL;

	/* Split the hash list up into sources and destinations */
	do {
		struct file_similarity *entry = p;
		p = p->next;
		if (entry->src_dst < 0) {
			entry->next = src;
			src = entry;
		} else {
			entry->next = dst;
			dst = entry;
		}
	} while (p);

	/*
	 * If we have both sources *and* destinations, see if
	 * we can match them up
	 */
	ret = (src && dst) ? find_identical_files(src, dst) : 0;

	/* Free the hashes and return the number of renames found */
	free_similarity_list(src);
	free_similarity_list(dst);
	return ret;
}

static unsigned int hash_filespec(struct diff_filespec *filespec)
{
	unsigned int hash;
	if (!filespec->sha1_valid) {
		if (diff_populate_filespec(filespec, 0))
			return 0;
		hash_sha1_file(filespec->data, filespec->size, "blob", filespec->sha1);
	}
	memcpy(&hash, filespec->sha1, sizeof(hash));
	return hash;
}

static void insert_file_table(struct hash_table *table, int src_dst, int index, struct diff_filespec *filespec)
{
	void **pos;
	unsigned int hash;
	struct file_similarity *entry = xmalloc(sizeof(*entry));

	entry->src_dst = src_dst;
	entry->index = index;
	entry->filespec = filespec;
	entry->next = NULL;

	hash = hash_filespec(filespec);
	pos = insert_hash(hash, entry, table);

	/* We already had an entry there? */
	if (pos) {
		entry->next = *pos;
		*pos = entry;
	}
}

/*
 * Find exact renames first.
 *
 * The first round matches up the up-to-date entries,
 * and then during the second round we try to match
 * cache-dirty entries as well.
 */
static int find_exact_renames(void)
{
	int i;
	struct hash_table file_table;

	init_hash(&file_table);
	for (i = 0; i < rename_src_nr; i++)
		insert_file_table(&file_table, -1, i, rename_src[i].one);

	for (i = 0; i < rename_dst_nr; i++) {
		if (rename_dst[i].i_am_not_single)
			continue;
		insert_file_table(&file_table, 1, i, rename_dst[i].two);
	}

	/* Find the renames */
	i = for_each_hash(&file_table, find_same_files);

	/* .. and free the hash data structure */
	free_hash(&file_table);

	return i;
}

#define NUM_CANDIDATE_PER_DST 4
static void record_if_better(struct diff_score m[], struct diff_score *o)
{
	int i, worst;

	/* find the worst one */
	worst = 0;
	for (i = 1; i < NUM_CANDIDATE_PER_DST; i++)
		if (score_compare(&m[i], &m[worst]) > 0)
			worst = i;

	/* is it better than the worst one? */
	if (score_compare(&m[worst], o) > 0)
		m[worst] = *o;
}

static struct diff_bulk_rename {
	struct diff_filespec *one;
	struct diff_filespec *two;
	int discarded;
} *bulkmove_candidates;
static int bulkmove_candidates_nr, bulkmove_candidates_alloc;

/*
 * Do a binary search of "one" in "bulkmove_candidate", inserting it if not
 * found.
 * A good part was copy-pasted from locate_rename_dst().
 */
static struct diff_bulk_rename *locate_bulkmove_candidate(const char *one_path,
							  const char *two_path)
{
	int first, last;

	first = 0;
	last = bulkmove_candidates_nr;
	while (last > first) {
		int next = (last + first) >> 1;
		struct diff_bulk_rename *candidate = &(bulkmove_candidates[next]);
		/* primary sort key on one_path, secondary on two_path */
		int cmp = strcmp(one_path, candidate->one->path);
		if (!cmp)
			cmp = strcmp(two_path, candidate->two->path);
		if (!cmp)
			return candidate;
		if (cmp < 0) {
			last = next;
			continue;
		}
		first = next+1;
	}
	/* not found */
	/* insert to make it at "first" */
	if (bulkmove_candidates_alloc <= bulkmove_candidates_nr) {
		bulkmove_candidates_alloc = alloc_nr(bulkmove_candidates_alloc);
		bulkmove_candidates = xrealloc(bulkmove_candidates,
				      bulkmove_candidates_alloc * sizeof(*bulkmove_candidates));
	}
	bulkmove_candidates_nr++;
	if (first < bulkmove_candidates_nr)
		memmove(bulkmove_candidates + first + 1, bulkmove_candidates + first,
			(bulkmove_candidates_nr - first - 1) * sizeof(*bulkmove_candidates));

	bulkmove_candidates[first].one = alloc_filespec(one_path);
	fill_filespec(bulkmove_candidates[first].one, null_sha1, S_IFDIR);
	bulkmove_candidates[first].two = alloc_filespec(two_path);
	fill_filespec(bulkmove_candidates[first].two, null_sha1, S_IFDIR);
	bulkmove_candidates[first].discarded = 0;
	return &(bulkmove_candidates[first]);
}

/*
 * Marks as such file_rename if it is made uninteresting by dir_rename.
 * Returns -1 if the file_rename is outside of the range in which given
 * renames concerned by dir_rename are to be found (ie. end of loop),
 * 0 otherwise.
 */
static int maybe_mark_uninteresting(struct diff_rename_dst *file_rename,
				    struct diff_bulk_rename *dir_rename,
				    int one_len, int two_len)
{
	if (!file_rename->pair) /* file add */
		return 0;
	if (strncmp(file_rename->two->path,
		    dir_rename->two->path, two_len))
		return -1;
	if (strncmp(file_rename->pair->one->path,
		    dir_rename->one->path, one_len) ||
	    !basename_same(file_rename->pair->one, file_rename->two) ||
	    file_rename->pair->score != MAX_SCORE)
		return 0;

	file_rename->pair->uninteresting_rename = 1;
	debug_bulkmove(("%s* -> %s* makes %s -> %s uninteresting\n",
			dir_rename->one->path, dir_rename->two->path,
			file_rename->pair->one->path, file_rename->two->path));
	return 0;
}

/*
 * Copy dirname of src into dst, suitable to append a filename without
 * an additional "/".
 * Only handles relative paths since there is no absolute path in a git repo.
 * Writes "" when there is no "/" in src.
 * May overwrite more chars than really needed, if src ends with a "/".
 * Supports in-place modification of src by passing dst == src.
 */
static const char *copy_dirname(char *dst, const char *src)
{
	size_t len = strlen(src);
	const char *slash;
	char *end;

	if (len > 0 && src[len - 1] == '/')
		/* Trailing slash.  Ignore it. */
		len--;

	slash = memrchr(src, '/', len);
	if (!slash) {
		*dst = '\0';
		return dst;
	}

	end = mempcpy(dst, src, slash - src + 1);
	*end = '\0';
	return dst;
}

// FIXME: leaks like hell.
/* See if the fact that one_leftover exists under one_parent_path in
 * dst tree should disqualify one_parent_path from bulkmove eligibility.
 * Return 1 if it disqualifies, 0 if it is OK.
 */
static int dispatched_to_different_dirs(const char *one_parent_path)
{
	/* this might be a dir split, or files added
	 * after the bulk move, or just an isolated
	 * rename */
	int two_idx, j, onep_len, maybe_dir_rename;
	struct diff_rename_dst *one_leftover =
		one_leftover = locate_rename_dst_dir(one_parent_path);

	if (!one_leftover)
		return 0;

	/* try to see if it is a file added after the bulk move */
	two_idx = one_leftover - rename_dst;
	onep_len = strlen(one_parent_path);
	maybe_dir_rename = 1;

	/* check no leftover file was already here before */
	for (j = two_idx; j < rename_dst_nr; j++) {
		if (strncmp(rename_dst[j].two->path,
			    one_parent_path, onep_len))
			break; /* exhausted directory in this direction */
		debug_bulkmove(("leftover file %s in %s\n",
				rename_dst[j].two->path, one_parent_path));
		if (rename_dst[j].i_am_not_single || /* those were already here */
		    (rename_dst[j].pair &&
		     !strncmp(rename_dst[j].pair->one->path,
			      one_parent_path, onep_len) && /* renamed from here */
		     strncmp(rename_dst[j].two->path,
			     one_parent_path, onep_len))) { /* not to a subdir */
			maybe_dir_rename = 0;
			debug_bulkmove(("... tells not a bulk move\n"));
			break;
		}
		debug_bulkmove(("... not believed to prevent bulk move\n"));
	}
	if (!maybe_dir_rename)
		return 1;
	/* try the other direction (dup code) */
	for (j = two_idx-1; j >= 0; j--) {
		if (strncmp(rename_dst[j].two->path,
			    one_parent_path, onep_len))
			break; /* exhausted directory in this direction */
		debug_bulkmove(("leftover file %s in '%s'\n",
				rename_dst[j].two->path, one_parent_path));
		if (rename_dst[j].i_am_not_single || /* those were already here */
		    (rename_dst[j].pair &&
		     !strncmp(rename_dst[j].pair->one->path,
			      one_parent_path, onep_len) && /* renamed from here */
		     strncmp(rename_dst[j].two->path,
			     one_parent_path, onep_len))) { /* not to a subdir */
			maybe_dir_rename = 0;
			debug_bulkmove(("... tells not a bulk move\n"));
			break;
		}
		debug_bulkmove(("... not believed to prevent bulk move\n"));
	}
	if (!maybe_dir_rename)
		return 1;

	/* Here we are in the case where a directory
	 * content was completely moved, but files
	 * were added to it afterwards.  Proceed as
	 * for a simple bulk move. */
	return 0;
}

/*
 * Assumes candidate->one is a subdir of seen->one, mark 'seen' as
 * discarded if candidate->two is outside seen->two.  Also mark
 * 'candidate' itself as discarded if the conflict implies so.
 *
 * Return 1 if 'seen' was discarded
 */
static int discard_if_outside(struct diff_bulk_rename *candidate,
			 struct diff_bulk_rename *seen) {
	if (!prefixcmp(candidate->two->path, seen->two->path)) {
		debug_bulkmove((" 'dstpair' conforts 'seen'\n"));
		return 0;
	} else {
		debug_bulkmove(("discarding %s -> %s from bulk moves (split into %s and %s)\n",
				seen->one->path, seen->two->path,
				candidate->two->path, seen->two->path));
		seen->discarded = 1;
		/* Need to discard dstpair as well, unless moving from
		 * a strict subdir of seen->one or to a strict subdir
		 * of seen->two */
		if (!strcmp(seen->one->path, candidate->one->path) &&
		    prefixcmp(seen->two->path, candidate->two->path)) {
			debug_bulkmove(("... and not adding self\n"));
			candidate->discarded = 1;
		}
		return 1;
	}
}

/*
 * Check if the rename specified by "dstpair" could cause a
 * bulk move to be detected, record it in bulkmove_candidates if yes.
 */
static void check_one_bulk_move(struct diff_filepair *dstpair)
{
	char one_parent_path[PATH_MAX], two_parent_path[PATH_MAX];

	/* genuine new files (or believed to be so) */
	if (!dstpair)
		return;
	/* dummy renames used by copy detection */
	if (!strcmp(dstpair->one->path, dstpair->two->path))
		return;

	copy_dirname(one_parent_path, dstpair->one->path);
	copy_dirname(two_parent_path, dstpair->two->path);

	/* simple rename with no directory change */
	if (!strcmp(one_parent_path, two_parent_path))
		return;

	debug_bulkmove(("[] %s -> %s ?\n", dstpair->one->path, dstpair->two->path));

	/* loop up one_parent_path over successive parents */
	// FIXME: also loop over two_parent_path prefixes
	do {
		struct diff_bulk_rename *seen;
		int old_nr = bulkmove_candidates_nr;
		struct diff_bulk_rename *candidate =
			locate_bulkmove_candidate(one_parent_path, two_parent_path);
		debug_bulkmove(("[[]] %s ...\n", one_parent_path));
		if (old_nr == bulkmove_candidates_nr) {
			debug_bulkmove((" already seen\n"));
			return;
		}

		/* After this commit, are there any files still under one_parent_path ?
		 * Any file left would disqualifies this dir for bulk move.
		 */
		if (dispatched_to_different_dirs(one_parent_path)) {
			// FIXME: check overlap with discard_if_outside()
			candidate->discarded = 1;
			return;
		}

		/* walk up for one_parent_path prefixes */
		for (seen = candidate-1; (seen >= bulkmove_candidates) &&
			     !prefixcmp(one_parent_path, seen->one->path); seen--) {
			debug_bulkmove((" ? %s -> %s\n", seen->one->path, seen->two->path));
			/* subdir of "seen" dest dir ? */
			if (discard_if_outside(candidate, seen))
				continue;
		}
		/* look down for other moves from one_parent_path */
		seen = candidate + 1;
		if (seen != bulkmove_candidates + bulkmove_candidates_nr &&
		    !strcmp(one_parent_path, seen->one->path)) {
			debug_bulkmove((" ? %s -> %s (2)\n", seen->one->path, seen->two->path));
			/* subdir of "seen" dest dir ? */
			if (discard_if_outside(candidate, seen))
				continue;
		}

		/* next parent if any */
		copy_dirname(one_parent_path, one_parent_path);
	} while (*one_parent_path);
}

/*
 * Take all file renames recorded so far and check if they could cause
 * a bulk move to be detected.
 */
static void diffcore_bulk_moves(int opt_hide_renames)
{
	int i;
	for (i = 0; i < rename_dst_nr; i++)
		check_one_bulk_move(rename_dst[i].pair);

	if (opt_hide_renames) {
		/* flag as "uninteresting" those candidates hidden by dir move */
		struct diff_bulk_rename *candidate;
		for (candidate = bulkmove_candidates;
		     candidate < bulkmove_candidates + bulkmove_candidates_nr;
		     candidate++) {
			int two_idx, i, one_len, two_len;
			struct diff_rename_dst *two_sample;
			if (candidate->discarded)
				continue;

			/* bisect to any entry within candidate dst dir */
			two_sample = locate_rename_dst_dir(candidate->two->path);
			if (!two_sample) {
				die("PANIC: %s candidate of rename not in target tree (from %s)\n",
				    candidate->two->path, candidate->one->path);
			}
			two_idx = two_sample - rename_dst;

			/* now remove extraneous 100% files inside. */
			one_len = strlen(candidate->one->path);
			two_len = strlen(candidate->two->path);
			for (i = two_idx; i < rename_dst_nr; i++)
				if (maybe_mark_uninteresting(rename_dst+i, candidate,
							     one_len, two_len) < 0)
					break;
			for (i = two_idx-1; i >= 0; i--)
				if (maybe_mark_uninteresting(rename_dst+i, candidate,
							     one_len, two_len) < 0)
					break;
		}
	}
}

void diffcore_rename(struct diff_options *options)
{
	int detect_rename = options->detect_rename;
	int minimum_score = options->rename_score;
	int rename_limit = options->rename_limit;
	struct diff_queue_struct *q = &diff_queued_diff;
	struct diff_queue_struct outq;
	struct diff_score *mx;
	int i, j, rename_count;
	int num_create, num_src, dst_cnt;
	struct diff_bulk_rename *candidate;

	if (!minimum_score)
		minimum_score = DEFAULT_RENAME_SCORE;

	for (i = 0; i < q->nr; i++) {
		struct diff_filepair *p = q->queue[i];
		if (!DIFF_FILE_VALID(p->one)) {
			if (!DIFF_FILE_VALID(p->two))
				continue; /* unmerged */
			else if (options->single_follow &&
				 strcmp(options->single_follow, p->two->path))
				continue; /* not interested */
			else
				locate_rename_dst(p->two, 1);
		} else if (!DIFF_FILE_VALID(p->two)) {
			/*
			 * If the source is a broken "delete", and
			 * they did not really want to get broken,
			 * that means the source actually stays.
			 * So we increment the "rename_used" score
			 * by one, to indicate ourselves as a user
			 */
			if (p->broken_pair && !p->score)
				p->one->rename_used++;
			register_rename_src(p->one, p->score);
		} else {
			if (detect_rename == DIFF_DETECT_COPY) {
				/*
				 * Increment the "rename_used" score by
				 * one, to indicate ourselves as a user.
				 */
				p->one->rename_used++;
				register_rename_src(p->one, p->score);
			}
			if (DIFF_OPT_TST(options, DETECT_BULK_MOVES)) {
				/* similarly, bulk move detection needs to
				 * see all files from second tree, but we don't
				 * want them to be matched against single sources.
				 */
				// FIXME: check interaction with --find-copies-harder
				locate_rename_dst(p->two, 1)->i_am_not_single = 1;
			}
		}
	}
	if (rename_dst_nr == 0 || rename_src_nr == 0)
		goto cleanup; /* nothing to do */

	/*
	 * We really want to cull the candidates list early
	 * with cheap tests in order to avoid doing deltas.
	 */
	rename_count = find_exact_renames();

	/* Did we only want exact renames? */
	if (minimum_score == MAX_SCORE)
		goto cleanup;

	/*
	 * Calculate how many renames are left (but all the source
	 * files still remain as options for rename/copies!)
	 */
	num_create = (rename_dst_nr - rename_count);
	num_src = rename_src_nr;

	/* All done? */
	if (!num_create)
		goto cleanup;

	/*
	 * This basically does a test for the rename matrix not
	 * growing larger than a "rename_limit" square matrix, ie:
	 *
	 *    num_create * num_src > rename_limit * rename_limit
	 *
	 * but handles the potential overflow case specially (and we
	 * assume at least 32-bit integers)
	 */
	if (rename_limit <= 0 || rename_limit > 32767)
		rename_limit = 32767;
	if ((num_create > rename_limit && num_src > rename_limit) ||
	    (num_create * num_src > rename_limit * rename_limit)) {
		if (options->warn_on_too_large_rename)
			warning("too many files (created: %d deleted: %d), skipping inexact rename detection", num_create, num_src);
		goto cleanup;
	}

	mx = xcalloc(num_create * NUM_CANDIDATE_PER_DST, sizeof(*mx));
	for (dst_cnt = i = 0; i < rename_dst_nr; i++) {
		struct diff_filespec *two = rename_dst[i].two;
		struct diff_score *m;

		if (rename_dst[i].pair)
			continue; /* dealt with exact match already. */
		if (rename_dst[i].i_am_not_single)
			continue; /* not looking for a match. */

		m = &mx[dst_cnt * NUM_CANDIDATE_PER_DST];
		for (j = 0; j < NUM_CANDIDATE_PER_DST; j++)
			m[j].dst = -1;

		for (j = 0; j < rename_src_nr; j++) {
			struct diff_filespec *one = rename_src[j].one;
			struct diff_score this_src;
			this_src.score = estimate_similarity(one, two,
							     minimum_score);
			this_src.name_score = basename_same(one, two);
			this_src.dst = i;
			this_src.src = j;
			record_if_better(m, &this_src);
			/*
			 * Once we run estimate_similarity,
			 * We do not need the text anymore.
			 */
			diff_free_filespec_blob(one);
			diff_free_filespec_blob(two);
		}
		dst_cnt++;
	}

	/* cost matrix sorted by most to least similar pair */
	qsort(mx, dst_cnt * NUM_CANDIDATE_PER_DST, sizeof(*mx), score_compare);

	for (i = 0; i < dst_cnt * NUM_CANDIDATE_PER_DST; i++) {
		struct diff_rename_dst *dst;

		if ((mx[i].dst < 0) ||
		    (mx[i].score < minimum_score))
			break; /* there is no more usable pair. */
		dst = &rename_dst[mx[i].dst];
		if (dst->pair)
			continue; /* already done, either exact or fuzzy. */
		if (rename_src[mx[i].src].one->rename_used)
			continue;
		record_rename_pair(mx[i].dst, mx[i].src, mx[i].score);
		rename_count++;
	}

	for (i = 0; i < dst_cnt * NUM_CANDIDATE_PER_DST; i++) {
		struct diff_rename_dst *dst;

		if ((mx[i].dst < 0) ||
		    (mx[i].score < minimum_score))
			break; /* there is no more usable pair. */
		dst = &rename_dst[mx[i].dst];
		if (dst->pair)
			continue; /* already done, either exact or fuzzy. */
		record_rename_pair(mx[i].dst, mx[i].src, mx[i].score);
		rename_count++;
	}
	free(mx);

 cleanup:
	/* At this point, we have found some renames and copies and they
	 * are recorded in rename_dst.  The original list is still in *q.
	 */

	/* Now possibly factorize those renames and copies. */
	if (DIFF_OPT_TST(options, DETECT_BULK_MOVES))
		diffcore_bulk_moves(DIFF_OPT_TST(options, HIDE_DIR_RENAME_DETAILS));

	DIFF_QUEUE_CLEAR(&outq);

	/* Now turn non-discarded bulkmove_candidates into real renames */
	for (candidate = bulkmove_candidates;
	     candidate < bulkmove_candidates + bulkmove_candidates_nr; candidate++) {
		struct diff_filepair* pair;
		if (candidate->discarded)
			continue;
		/* visualize toplevel dir if needed */
		if (!*candidate->one->path)
			candidate->one->path = "./";
		if (!*candidate->two->path)
			candidate->two->path = "./";
		pair = diff_queue(&outq, candidate->one, candidate->two);
		pair->score = MAX_SCORE;
		pair->renamed_pair = 1;
		pair->is_bulkmove = 1;
	}

	for (i = 0; i < q->nr; i++) {
		struct diff_filepair *p = q->queue[i];
		struct diff_filepair *pair_to_free = NULL;

		if (!DIFF_FILE_VALID(p->one) && DIFF_FILE_VALID(p->two)) {
			/*
			 * Creation
			 *
			 * We would output this create record if it has
			 * not been turned into a rename/copy already.
			 */
			struct diff_rename_dst *dst =
				locate_rename_dst(p->two, 0);
			if (dst && dst->pair) {
				if (!dst->pair->uninteresting_rename)
					diff_q(&outq, dst->pair);
				pair_to_free = p;
			}
			else
				/* no matching rename/copy source, so
				 * record this as a creation.
				 */
				diff_q(&outq, p);
		}
		else if (DIFF_FILE_VALID(p->one) && !DIFF_FILE_VALID(p->two)) {
			/*
			 * Deletion
			 *
			 * We would output this delete record if:
			 *
			 * (1) this is a broken delete and the counterpart
			 *     broken create remains in the output; or
			 * (2) this is not a broken delete, and rename_dst
			 *     does not have a rename/copy to move p->one->path
			 *     out of existence.
			 *
			 * Otherwise, the counterpart broken create
			 * has been turned into a rename-edit; or
			 * delete did not have a matching create to
			 * begin with.
			 */
			if (DIFF_PAIR_BROKEN(p)) {
				/* broken delete */
				struct diff_rename_dst *dst =
					locate_rename_dst(p->one, 0);
				if (dst && dst->pair)
					/* counterpart is now rename/copy */
					pair_to_free = p;
			}
			else {
				if (p->one->rename_used)
					/* this path remains */
					pair_to_free = p;
			}

			if (pair_to_free)
				;
			else
				diff_q(&outq, p);
		}
		else if (!diff_unmodified_pair(p))
			/* all the usual ones need to be kept */
			diff_q(&outq, p);
		else
			/* no need to keep unmodified pairs */
			pair_to_free = p;

		if (pair_to_free)
			diff_free_filepair(pair_to_free);
	}
	diff_debug_queue("done copying original", &outq);

	free(q->queue);
	*q = outq;
	diff_debug_queue("done collapsing", q);

	for (i = 0; i < rename_dst_nr; i++)
		free_filespec(rename_dst[i].two);

	free(rename_dst);
	rename_dst = NULL;
	rename_dst_nr = rename_dst_alloc = 0;
	free(rename_src);
	rename_src = NULL;
	rename_src_nr = rename_src_alloc = 0;
	return;
}
