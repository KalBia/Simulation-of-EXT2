/*
 * Oświadczam, że zapoznałem(-am) się z regulaminem prowadzenia zajęć
 * i jestem świadomy(-a) konsekwencji niestosowania się do podanych tam zasad.
 */
#ifdef STUDENT
/* Imię i nazwisko, numer indeksu: Kalina Białek, 340152 */
#endif

#include <assert.h>
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <stdalign.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <unistd.h>

#include "ext2fs_defs.h"
#include "ext2fs.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#undef DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* Call this function when an unfixable error has happened. */
static noreturn void panic(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  fputc('\n', stderr);
  va_end(ap);
  exit(EXIT_FAILURE);
}

/* Number of lists containing buffered blocks. */
#define NBUCKETS 16

/* Since majority of files in a filesystem are small, `idx` values will be
 * usually low. Since ext2fs tends to allocate blocks at the beginning of each
 * block group, `ino` values are less predictable. */
#define BUCKET(ino, idx) (((ino) + (idx)) % NBUCKETS)

/* That should give us around 64kB worth of buffers. */
#define NBLOCKS (NBUCKETS * 4)

/* Structure that is used to manage buffer of single block. */
typedef struct blk {
  TAILQ_ENTRY(blk) b_hash;
  TAILQ_ENTRY(blk) b_link;
  uint32_t b_blkaddr; /* block address on the block device */
  uint32_t b_inode;   /* i-node number of file this buffer refers to */
  uint32_t b_index;   /* block index from the beginning of file */
  uint32_t b_refcnt;  /* if zero then block can be reused */
  void *b_data;       /* raw data from this buffer */
} blk_t;

typedef TAILQ_HEAD(blk_list, blk) blk_list_t;

/* BLK_ZERO is a special value that reflect the fact that block 0 may be used to
 * represent a block filled with zeros. You must not dereference the value! */
#define BLK_ZERO ((blk_t *)-1L)

/* All memory for buffers and buffer management is allocated statically.
 * Using malloc for these would introduce unnecessary complexity. */
static alignas(BLKSIZE) char blkdata[NBLOCKS][BLKSIZE];
static blk_t blocks[NBLOCKS];
static blk_list_t buckets[NBUCKETS]; /* all blocks with valid data */
static blk_list_t lrulst;            /* free blocks with valid data */
static blk_list_t freelst;           /* free blocks that are empty */

/* File descriptor that refers to ext2 filesystem image. */
static int fd_ext2 = -1;

/* How many i-nodes fit into one block? */
#define BLK_INODES (BLKSIZE / sizeof(ext2_inode_t))

/* How many block pointers fit into one block? */
#define BLK_POINTERS (BLKSIZE / sizeof(uint32_t))

/* Properties extracted from a superblock and block group descriptors. */
static size_t inodes_per_group;      /* number of i-nodes in block group */
static size_t blocks_per_group;      /* number of blocks in block group */
static size_t group_desc_count;      /* numbre of block group descriptors */
static size_t block_count;           /* number of blocks in the filesystem */
static size_t inode_count;           /* number of i-nodes in the filesystem */
static size_t first_data_block;      /* first block managed by block bitmap */
static ext2_groupdesc_t *group_desc; /* block group descriptors in memory */

/*
 * Buffering routines.
 */

/* Opens filesystem image file and initializes block buffers. */
static int blk_init(const char *fspath) {
  if ((fd_ext2 = open(fspath, O_RDONLY)) < 0)
    return errno;

  /* Initialize list structures. */
  TAILQ_INIT(&lrulst);
  TAILQ_INIT(&freelst);
  for (int i = 0; i < NBUCKETS; i++)
    TAILQ_INIT(&buckets[i]);

  /* Initialize all blocks and put them on free list. */
  for (int i = 0; i < NBLOCKS; i++) {
    blocks[i].b_data = blkdata[i];
    TAILQ_INSERT_TAIL(&freelst, &blocks[i], b_link);
  }

  return 0;
}

/* Allocates new block buffer. */
static blk_t *blk_alloc(void) {
  blk_t *blk = NULL;

  /* Initially every empty block is on free list. */
  if (!TAILQ_EMPTY(&freelst)) {
#ifdef STUDENT

    /* Get first free block from the list. */
    blk = TAILQ_FIRST(&freelst);

    /* Remove this block from the list. */
    TAILQ_REMOVE(&freelst, blk, b_link);

#endif /* !STUDENT */
    return blk;
  }

  /* Eventually free list will become exhausted.
   * Then we'll take the last recently used entry from LRU list. */
  if (!TAILQ_EMPTY(&lrulst)) {
#ifdef STUDENT

    /* Get last block from LRU list - the least recently used one. */
    blk = TAILQ_LAST(&lrulst, blk_list);

    /* Remove this block from the list. */
    TAILQ_REMOVE(&lrulst, blk, b_link);

    /* Remove this block from buckets array. */
    /* In which bucket is it? */
    blk_list_t *bucket = &buckets[BUCKET(blk->b_inode, blk->b_index)];
    /* Remove. */
    TAILQ_REMOVE(bucket, blk, b_hash);

#endif /* !STUDENT */
    return blk;
  }

  /* No buffers!? Have you forgot to release some? */
  panic("Free buffers pool exhausted!");
}

/* Acquires a block buffer for file identified by `ino` i-node and block index
 * `idx`. When `ino` is zero the buffer refers to filesystem metadata (i.e.
 * superblock, block group descriptors, block & i-node bitmap, etc.) and `off`
 * offset is given from the start of block device. */
static blk_t *blk_get(uint32_t ino, uint32_t idx) {
  blk_list_t *bucket = &buckets[BUCKET(ino, idx)];
  blk_t *blk = NULL;

  /* Locate a block in the buffer and return it if found. */
#ifdef STUDENT

  /* We want to check if we already have this data in the buffer.
   * First, check if it is in the bucket, if yes - return it.
   * Otherwise, after "student area" we allocate a block for it
   * and put there the data from filesystem. */

  TAILQ_FOREACH (blk, bucket, b_hash) {
    if (blk->b_inode == ino && blk->b_index == idx) {
      /* Found it! We need to check, if it is on LRU list. */
      if (blk->b_refcnt == 0)
        TAILQ_REMOVE(&lrulst, blk, b_link);

      /* Increment reference count, because we reference it :D */
      blk->b_refcnt++;

      return blk;
    }
  }

#endif /* !STUDENT */

  long blkaddr = ext2_blkaddr_read(ino, idx);
  debug("ext2_blkaddr_read(%d, %d) -> %ld\n", ino, idx, blkaddr);
  if (blkaddr == -1)
    return NULL;
  if (blkaddr == 0)
    return BLK_ZERO;
  if (ino > 0 && !ext2_block_used(blkaddr))
    panic("Attempt to read block %d that is not in use!", blkaddr);

  blk = blk_alloc();
  blk->b_inode = ino;
  blk->b_index = idx;
  blk->b_blkaddr = blkaddr;
  blk->b_refcnt = 1;

  ssize_t nread =
    pread(fd_ext2, blk->b_data, BLKSIZE, blk->b_blkaddr * BLKSIZE);
  if (nread != BLKSIZE)
    panic("Attempt to read past the end of filesystem!");

  TAILQ_INSERT_HEAD(bucket, blk, b_hash);
  return blk;
}

/* Releases a block buffer. If reference counter hits 0 the buffer can be
 * reused to cache another block. The buffer is put at the beginning of LRU list
 * of unused blocks. */
static void blk_put(blk_t *blk) {
  if (--blk->b_refcnt > 0)
    return;

  TAILQ_INSERT_HEAD(&lrulst, blk, b_link);
}

/*
 * Ext2 filesystem routines.
 */

/* Reads block bitmap entry for `blkaddr`. Returns 0 if the block is free,
 * 1 if it's in use, and EINVAL if `blkaddr` is out of range. */
int ext2_block_used(uint32_t blkaddr) {
  if (blkaddr >= block_count)
    return EINVAL;
  int used = 0;
#ifdef STUDENT

  /* Which block group?
   * Remember that addresses start at 1! */
  size_t block_group = (blkaddr - 1) / blocks_per_group;

  /* Get the right block bitmap from buffer (!) - so we need to use blk_get.
   * 1st: blk_get - "When `ino` is zero the buffer refers to filesystem
   * metadata". 2nd: "Its official location can be determined by reading the
   * “bg_block_bitmap” in its associated group descriptor." -> so it's just an
   * address aka our idx. */
  blk_t *blk = blk_get(0, group_desc[block_group].gd_b_bitmap);

  /* Get the raw data of this block. */
  uint8_t *bitmap = (uint8_t *)blk->b_data;

  /* Check the right bit.
   * "Each bit represent the current state of a block within that block group,
   * where 1 means “used” and 0 “free/available”. The first block of this block
   * group is represented by bit 0 of byte 0, the second by bit 1 of byte 0.
   * The 8th block is represented by bit 7 (most significant bit) of byte 0
   * while the 9th block is represented by bit 0 (least significant bit) of
   * byte 1." */
  uint32_t bit_index = (blkaddr - 1) % blocks_per_group;
  uint32_t byte_index = bit_index / 8;
  uint8_t bit_offset = bit_index % 8;
  used = (bitmap[byte_index] & (1 << bit_offset)) >> bit_offset;

  /* Put the block back. */
  blk_put(blk);

#endif /* !STUDENT */
  return used;
}

/* Reads i-node bitmap entry for `ino`. Returns 0 if the i-node is free,
 * 1 if it's in use, and EINVAL if `ino` value is out of range. */
int ext2_inode_used(uint32_t ino) {
  if (!ino || ino >= inode_count)
    return EINVAL;
  int used = 0;
#ifdef STUDENT

  /* Which block group?
   * Remember that inodes start at 1! */
  size_t block_group = (ino - 1) / inodes_per_group;

  /* Get the right inode bitmap from buffer (!) - so we need to use blk_get.
   * 1st: blk_get - "When `ino` is zero the buffer refers to filesystem
   * metadata". 2nd: "its location may be determined by reading the
   * “bg_inode_bitmap” in its associated group descriptor." -> so it's just an
   * address aka our idx. */
  blk_t *blk = blk_get(0, group_desc[block_group].gd_i_bitmap);

  /* Get the raw data of this block. */
  uint8_t *bitmap = (uint8_t *)blk->b_data;

  /* Check the right bit.
   * "Each bit represent the current state of a block within that block group,
   * where 1 means “used” and 0 “free/available”. The first block of this block
   * group is represented by bit 0 of byte 0, the second by bit 1 of byte 0.
   * The 8th block is represented by bit 7 (most significant bit) of byte 0
   * while the 9th block is represented by bit 0 (least significant bit) of
   * byte 1." */
  uint32_t bit_index = (ino - 1) % inodes_per_group;
  uint32_t byte_index = bit_index / 8;
  uint8_t bit_offset = bit_index % 8;
  used = (bitmap[byte_index] & (1 << bit_offset)) >> bit_offset;

  /* Put the block back. */
  blk_put(blk);

#endif /* !STUDENT */
  return used;
}

/* Reads i-node identified by number `ino`.
 * Returns 0 on success. If i-node is not allocated returns ENOENT. */
static int ext2_inode_read(off_t ino, ext2_inode_t *inode) {
#ifdef STUDENT

  int used = ext2_inode_used((uint32_t)ino);
  if (!used || used == EINVAL)
    return ENOENT;

  /* Which block group?
   * Remember that inodes start at 1! */
  size_t block_group = (ino - 1) / inodes_per_group;

  /* Which inode table entry? */
  uint32_t inode_table_offset =
    ((ino - 1) % inodes_per_group) * sizeof(ext2_inode_t);
  uint32_t block_offset = inode_table_offset / BLKSIZE;
  uint32_t in_block_offset = inode_table_offset % BLKSIZE;

  /* Get the right block from buffer (!) - so we need to use blk_get.
   * Afaik i-node table is not technically filesystem metadata, but it's not
   * data from a file of i-node neither, so I would say that it is still
   * closer to metadata and should act like one. */
  blk_t *blk = blk_get(0, group_desc[block_group].gd_i_tables + block_offset);

  /* "Copy" inode. */
  memcpy(inode, blk->b_data + in_block_offset, sizeof(ext2_inode_t));

  /* Put the block back. */
  blk_put(blk);

#endif /* !STUDENT */
  return 0;
}

/* Returns block pointer `blkidx` from block of `blkaddr` address. */
static uint32_t ext2_blkptr_read(uint32_t blkaddr, uint32_t blkidx) {
#ifdef STUDENT

  int used = ext2_block_used(blkaddr);
  if (!used || used == EINVAL)
    return 0;

  /* blkaddr is the address of block on block device, so we can use
   * blk_get with ino = 0. */
  blk_t *blk = blk_get(0, blkaddr);

  /* Get the block pointer. */
  uint32_t blkptr = ((uint32_t *)blk->b_data)[blkidx];

  /* Put the block back. */
  blk_put(blk);

  return blkptr;

#endif /* !STUDENT */
  return 0;
}

/* Translates i-node number `ino` and block index `idx` to block address.
 * Returns -1 on failure, otherwise block address. */
long ext2_blkaddr_read(uint32_t ino, uint32_t blkidx) {
  /* No translation for filesystem metadata blocks. */
  if (ino == 0)
    return blkidx;

  ext2_inode_t inode;
  if (ext2_inode_read(ino, &inode))
    return -1;

    /* Read direct pointers or pointers from indirect blocks. */
#ifdef STUDENT

  /* Numbers of indirect blocks */
  uint32_t single_indirect_boundary = EXT2_NADDR + BLK_POINTERS;
  uint32_t double_indirect_boundary =
    single_indirect_boundary + BLK_POINTERS * BLK_POINTERS;

  /* direct blocks */
  if (blkidx < EXT2_NADDR) {
    return inode.i_blocks[blkidx];
  }
  /* single indirect blocks */
  else if (blkidx < single_indirect_boundary) {
    /* first level
     * We move blkidx as if the direct blocks didn't exist and then we calculate
     * the address. */
    uint32_t indirect_idx = blkidx - EXT2_NADDR;
    return ext2_blkptr_read(inode.i_blocks[EXT2_NDADDR], indirect_idx);
  }
  /* double indirect blocks */
  else if (blkidx < double_indirect_boundary) {
    /* first level
     * We move blkidx as if neither direct nor single indirect blocks didn't
     * exist and then we calculate in which "single bucket" we need to look
     * next. */
    uint32_t indirect_idx = (blkidx - single_indirect_boundary) / BLK_POINTERS;
    uint32_t blkidx2 =
      ext2_blkptr_read(inode.i_blocks[EXT2_NDADDR + 1], indirect_idx);

    /* second level
     * Modulo makes an illusion as if this "single bucket" was the only bucket,
     * so indirect_idx is correct. */
    indirect_idx = (blkidx - single_indirect_boundary) % BLK_POINTERS;
    return ext2_blkptr_read(blkidx2, indirect_idx);
  }
  /* triple indirect blocks - all works as before but we move three levels. */
  else {
    /* first level */
    uint32_t indirect_idx =
      (blkidx - double_indirect_boundary) / (BLK_POINTERS * BLK_POINTERS);
    uint32_t blkidx2 =
      ext2_blkptr_read(inode.i_blocks[EXT2_NDADDR + 2], indirect_idx);

    /* second level */
    indirect_idx =
      ((blkidx - double_indirect_boundary) % (BLK_POINTERS * BLK_POINTERS)) /
      BLK_POINTERS;
    blkidx2 = ext2_blkptr_read(blkidx2, indirect_idx);

    /* third level */
    indirect_idx =
      ((blkidx - double_indirect_boundary) % (BLK_POINTERS * BLK_POINTERS)) %
      BLK_POINTERS;
    return ext2_blkptr_read(blkidx2, indirect_idx);
  }

#endif /* !STUDENT */
  return -1;
}

/* Reads exactly `len` bytes starting from `pos` position from any file (i.e.
 * regular, directory, etc.) identified by `ino` i-node. Returns 0 on success,
 * EINVAL if `pos` and `len` would have pointed past the last block of file.
 *
 * WARNING: This function assumes that `ino` i-node pointer is valid! */
int ext2_read(uint32_t ino, void *data, size_t pos, size_t len) {
#ifdef STUDENT

  /* We need (and can) check if 'pos' and 'len' would have pointed past the last
   * block of file only for 'ino' that is not 0 aka filesystem metadata. */
  if (ino) {
    ext2_inode_t inode;
    if (ext2_inode_read(ino, &inode))
      panic("couldn't read inode: %d", ino);

    /* "EINVAL if `pos` and `len` would have pointed past the last block of
     * file." */
    if ((pos + len) > inode.i_size)
      return EINVAL;
  }

  /* Calculate first and last block index. */
  uint32_t start_blkidx = pos / BLKSIZE;
  uint32_t end_blkidx = (pos + len) / BLKSIZE;

  /* Get the data from blocks. */
  while (start_blkidx <= end_blkidx) {
    blk_t *blk = blk_get(ino, start_blkidx);

    /* How many bytes from this block? */
    size_t copy_len = min(len, BLKSIZE - (pos % BLKSIZE));

    /* Copy data. */
    if (blk == BLK_ZERO) /* "You must not dereference the value!" */
      memset(data, 0, copy_len);
    else {
      memcpy(data, blk->b_data + (pos % BLKSIZE), copy_len);
      blk_put(blk);
    }

    /* Prepare for next step in loop. */
    pos += copy_len;
    data += copy_len;
    len -= copy_len;
    start_blkidx++;
  }

  return 0;

#endif /* !STUDENT */
  return EINVAL;
}

/* Reads a directory entry at position stored in `off_p` from `ino` i-node that
 * is assumed to be a directory file. The entry is stored in `de` and
 * `de->de_name` must be NUL-terminated. Assumes that entry offset is 0 or was
 * set by previous call to `ext2_readdir`. Returns 1 on success, 0 if there are
 * no more entries to read. */
#define de_name_offset offsetof(ext2_dirent_t, de_name)

int ext2_readdir(uint32_t ino, uint32_t *off_p, ext2_dirent_t *de) {
#ifdef STUDENT

  /* "Assumes that entry offset is 0 or was set by previous call to
   * `ext2_readdir`." */
  uint32_t offset;
  if (!off_p)
    offset = 0;
  else
    offset = *off_p;

  /* Get inode of directory. */
  ext2_inode_t inode;
  if (ext2_inode_read(ino, &inode))
    panic("couldn't read inode: %d", ino);

  /* Get the entry from offset, but if it is empty, skip it and give next one.
   */
  while (inode.i_size > offset) {
    /* Read "metadata" about entry. */
    if (ext2_read(ino, de, offset, de_name_offset))
      panic("couldn't read the entry: %d, %d", ino, offset);

    /* If empty -> skip the entry. */
    if (!de->de_ino) {
      offset += de->de_reclen;
      continue;
    }

    /* If not empty -> this is our entry! Read name. */
    if (ext2_read(ino, de->de_name, offset + de_name_offset, de->de_namelen))
      panic("couldn't read name in the entry: %d, %d", ino, offset);

    /* "`de->de_name` must be NUL-terminated." */
    de->de_name[de->de_namelen] = '\0';

    /* "Assumes that entry offset [...] was set by previous call to
     * `ext2_readdir`." */
    *off_p = offset + de->de_reclen;

    return 1;
  }

#endif /* !STUDENT */
  return 0;
}

/* Read the target of a symbolic link identified by `ino` i-node into buffer
 * `buf` of size `buflen`. Returns 0 on success, EINVAL if the file is not a
 * symlink or read failed. */
int ext2_readlink(uint32_t ino, char *buf, size_t buflen) {
  int error;

  ext2_inode_t inode;
  if ((error = ext2_inode_read(ino, &inode)))
    return error;

    /* Check if it's a symlink and read it. */
#ifdef STUDENT

  /* Check if it's not a symlink
   * or
   * if symlink size is bigger than buffer's size.
   * Why +1? We make it NULL-terminated, so we need it a bit bigger. */
  if (!(inode.i_mode & EXT2_IFLNK) || inode.i_size + 1 > buflen)
    return EINVAL;

  /* Read it. */
  /* If it's short enugh, read it from inode. */
  if (inode.i_size <= EXT2_MAXSYMLINKLEN)
    memcpy(buf, inode.i_blocks, inode.i_size);
  /* Else read it from data block. */
  else {
    if (ext2_read(ino, buf, 0, inode.i_size))
      panic("couldn't read the symlink: %d", ino);
  }

  /* Make it NULL-terminated. */
  buf[inode.i_size] = '\0';

  return 0;

#endif /* !STUDENT */
  return ENOTSUP;
}

/* Read metadata from file identified by `ino` i-node and convert it to
 * `struct stat`. Returns 0 on success, or error if i-node could not be read. */
int ext2_stat(uint32_t ino, struct stat *st) {
  int error;

  ext2_inode_t inode;
  if ((error = ext2_inode_read(ino, &inode)))
    return error;

    /* Convert the metadata! */
#ifdef STUDENT

  st->st_ino = ino;
  st->st_mode = inode.i_mode;
  st->st_nlink = inode.i_nlink;
  st->st_uid = inode.i_uid;
  st->st_gid = inode.i_gid;
  st->st_size = inode.i_size;
  st->st_blksize = BLKSIZE;
  st->st_blocks =
    (inode.i_nblock * BLKSIZE) / 512 + (inode.i_nblock * BLKSIZE % 512 ? 1 : 0);
  st->st_atime = inode.i_atime;
  st->st_mtime = inode.i_mtime;
  st->st_ctime = inode.i_ctime;

  /* We can't get the information about the device from what we have :c
   * So I will just skip this two steps, but they would look probably like this:
   *
   * Set st_dev.
   *  <somehow>
   *
   * Set st_rdev base on file type.
   * This field is used for special files representing devices (character or
   * block). For regular files, directories, and symbolic links, st_rdev is
   * typically set to 0. For special device files (character or block devices),
   * st_rdev holds the device ID. if( (inode.i_mode & EXT2_IFCHR) ||
   * (inode.i_mode & EXT2_IFBLK) ) st->st_rdev = st_dev; else st->st_rdev = 0;
   */

#endif /* !STUDENT */
  return ENOTSUP;
}

/* Reads file identified by `ino` i-node as directory and performs a lookup of
 * `name` entry. If an entry is found, its i-inode number is stored in `ino_p`
 * and its type in stored in `type_p`. On success returns 0, or EINVAL if `name`
 * is NULL or zero length, or ENOTDIR is `ino` file is not a directory, or
 * ENOENT if no entry was found. */
int ext2_lookup(uint32_t ino, const char *name, uint32_t *ino_p,
                uint8_t *type_p) {
  int error;

  if (name == NULL || !strlen(name))
    return EINVAL;

  ext2_inode_t inode;
  if ((error = ext2_inode_read(ino, &inode)))
    return error;

#ifdef STUDENT

  /* Check if 'ino' file is not a directory. */
  if (!(inode.i_mode & EXT2_IFDIR))
    return ENOTDIR;

  uint32_t offset = 0;
  ext2_dirent_t de;
  /* While there are still entries in directory. */
  while (ext2_readdir(ino, &offset, &de)) {
    /* If entry name with name we are looking for are equal. */
    if (!strcmp(de.de_name, name)) {
      *ino_p = de.de_ino;
      *type_p = de.de_type;

      return 0;
    }
  }

#endif /* !STUDENT */

  return ENOENT;
}

/* Initializes ext2 filesystem stored in `fspath` file.
 * Returns 0 on success, otherwise an error. */
int ext2_mount(const char *fspath) {
  int error;

  if ((error = blk_init(fspath)))
    return error;

  /* Read superblock and verify we support filesystem's features. */
  ext2_superblock_t sb;
  ext2_read(0, &sb, EXT2_SBOFF, sizeof(ext2_superblock_t));

  debug(">>> super block\n"
        "# of inodes      : %d\n"
        "# of blocks      : %d\n"
        "block size       : %ld\n"
        "blocks per group : %d\n"
        "inodes per group : %d\n"
        "inode size       : %d\n",
        sb.sb_icount, sb.sb_bcount, 1024UL << sb.sb_log_bsize, sb.sb_bpg,
        sb.sb_ipg, sb.sb_inode_size);

  if (sb.sb_magic != EXT2_MAGIC)
    panic("'%s' cannot be identified as ext2 filesystem!", fspath);

  if (sb.sb_rev != EXT2_REV1)
    panic("Only ext2 revision 1 is supported!");

  size_t blksize = 1024UL << sb.sb_log_bsize;
  if (blksize != BLKSIZE)
    panic("ext2 filesystem with block size %ld not supported!", blksize);

  if (sb.sb_inode_size != sizeof(ext2_inode_t))
    panic("The only i-node size supported is %d!", sizeof(ext2_inode_t));

    /* Load interesting data from superblock into global variables.
     * Read group descriptor table into memory. */
#ifdef STUDENT

  /* Load interesting data from superblock into global variables. */
  inodes_per_group = sb.sb_ipg;
  blocks_per_group = sb.sb_bpg;
  block_count = sb.sb_bcount;
  inode_count = sb.sb_icount;
  first_data_block = sb.sb_first_dblock;

  /* Calculate the number of group descriptors. */
  group_desc_count =
    (block_count / blocks_per_group) + (block_count % blocks_per_group ? 1 : 0);

  /* Read group descriptor table into memory. */
  if (!(group_desc = malloc(group_desc_count * sizeof(ext2_groupdesc_t))))
    panic("couldn't allocate memory for group descriptor table!\n");

  if (ext2_read(0, group_desc, EXT2_GDOFF,
                group_desc_count * sizeof(ext2_groupdesc_t)))
    panic("couldn't load group descriptor table!\n");

  return 0;

#endif /* !STUDENT */
  return ENOTSUP;
}
