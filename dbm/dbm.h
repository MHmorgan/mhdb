/*
 * Comments added for rust rewrite
 */

#define PBLKSIZ 512  /* pek file bulk size */
#define DBLKSIZ 8192 /* dir file bulk size */
#define BYTESIZ 8
#define NULL ((char *) 0)

/*
 * blkno = hash & hmask
 * bitno = blkno + hmask
 * 
 * hash  => 1001 1101 (0x9d 157)
 * hmask => 0000 1111 (0x0f 15)
 * blkno => 0000 1101 (0x0d 13)
 * bitno => 0001 1100 (0x1c 28)
 */
long    bitno;  /* Bit position in dir file */
long    maxbno; /* Max bulk number of dir file - bit size of file */
long    blkno;  /* pag bulk number */
long    hmask;  /* Hash mask with consecutiv ones in lower bits */

char    pagbuf[PBLKSIZ]; /* Read buffer for pag file */
char    dirbuf[DBLKSIZ]; /* Read buffer for dir file */

int dirf; /* .dir file pointer */
int pagf; /* .pag file pointer */

/*
 * The datum object points to sub-array inside the pagbuf
 */
typedef struct
{
    char *dptr;
    int dsize;
} datum;

datum   fetch();
datum   makdatum();
datum   firstkey();
datum   nextkey();
datum   firsthash();
long    calchash();
long    hashinc();