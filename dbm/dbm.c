/*
 * Comments added for rust rewrite
 */

#include    "dbm.h"
#include    <sys/types.h>
#include    <sys/stat.h>
#include    <stdio.h>
#include    <stdlib.h>
#include    <string.h>
#include    <unistd.h>

/* Open the two files associated with the database:
 *  <file>.pag
 *  <file>.dir
 * 
 * Sets maxbno to .dir file size (bits)
 */
dbminit(file)
char *file;
{
    struct stat statb;

    strcpy(pagbuf, file);
    strcat(pagbuf, ".pag");
    pagf = open(pagbuf, 2);

    strcpy(pagbuf, file);
    strcat(pagbuf, ".dir");
    dirf = open(pagbuf, 2);
    if(pagf < 0 || dirf < 0) {
        printf("cannot open database %s\n", file);
        return(-1);
    }
    fstat(dirf, &statb);
    maxbno = statb.st_size*BYTESIZ-1;
    return(0);
}

long
forder(key)
datum key;
{
    long hash;

    hash = calchash(key);
    for(hmask=0;; hmask=(hmask<<1)+1) {
        blkno = hash & hmask;
        bitno = blkno + hmask;
        if(getbit() == 0)
            break;
    }
    return(blkno);
}

/*
 * Return datum for data associated with key.
 * Data pointer is NULL on failure.
 */
datum
fetch(key)
datum key;
{
    register i;
    datum item;

    dbm_access(calchash(key));
    for(i=0;; i+=2) {
        item = makdatum(pagbuf, i);
        if(item.dptr == NULL)
            return(item);
        if(cmpdatum(key, item) == 0) {
            item = makdatum(pagbuf, i+1);
            if(item.dptr == NULL)
                printf("items not in pairs\n");
            return(item);
        }
    }
}

/*
 * Remove key-value pair from database
 */
delete(key)
datum key;
{
    register i;
    datum item;

    dbm_access(calchash(key));
    for(i=0;; i+=2) {
        item = makdatum(pagbuf, i);
        if(item.dptr == NULL)
            return(-1);
        if(cmpdatum(key, item) == 0) {
            delitem(pagbuf, i);
            delitem(pagbuf, i);
            break;
        }
    }
    lseek(pagf, blkno*PBLKSIZ, 0);
    write(pagf, pagbuf, PBLKSIZ);
    return(0);
}

/*
 * Store a key-value pair in the database.
 * If it already exists the previous key-value pair is deleted.
 * A key-value pair must fit within a single pag block.
 */
store(key, dat)
datum key, dat;
{
    register i;
    datum item;
    char ovfbuf[PBLKSIZ];

loop:
    /* fill pagbuf with block from pag */
    dbm_access(calchash(key));

    /* check if key already exists in block */
    for(i=0;; i+=2) {
        item = makdatum(pagbuf, i);

        if(item.dptr == NULL)
            break; /* continue if key doesn't exist */

        /* if key already exists remove previous data and key */
        if(cmpdatum(key, item) == 0) {
            delitem(pagbuf, i);
            delitem(pagbuf, i);
            break;
        }
    }

    i = additem(pagbuf, key);
    if(i < 0)
        goto split;
    if(additem(pagbuf, dat) < 0) {
        delitem(pagbuf, i);
        goto split;
    }
    lseek(pagf, blkno*PBLKSIZ, 0);
    write(pagf, pagbuf, PBLKSIZ);
    return;

split:
    if(key.dsize+dat.dsize+2*sizeof(short) >= PBLKSIZ) {
        printf("entry too big\n");
        return;
    }
    clrbuf(ovfbuf, PBLKSIZ);

    for(i=0;;) {
        item = makdatum(pagbuf, i);
        if(item.dptr == NULL)
            break;
        if(calchash(item) & (hmask+1)) { /* next pag blkno */
            /* move old items into ovfbuf */
            additem(ovfbuf, item);
            delitem(pagbuf, i);
            item = makdatum(pagbuf, i);
            if(item.dptr == NULL) {
                printf("split not paired\n");
                break;
            }
            additem(ovfbuf, item);
            delitem(pagbuf, i);
            continue;
        }
        i += 2;
    }

    /* write split pagbuf to blkno */
    lseek(pagf, blkno*PBLKSIZ, 0);
    write(pagf, pagbuf, PBLKSIZ);

    /* write ovfbuf next bulk in hash mask sequence */
    lseek(pagf, (blkno+hmask+1)*PBLKSIZ, 0);
    write(pagf, ovfbuf, PBLKSIZ);
    /* indicate that the current block has been split */
    setbit();

    goto loop;
}

/*
 * Return datum of first key in the database.
 */
datum
firstkey()
{
    return(firsthash(0L));
}

datum
nextkey(key)
datum key;
{
    register i;
    datum item, bitem;
    long hash;
    int f;

    hash = calchash(key);
    dbm_access(hash);
    f = 1;
    for(i=0;; i+=2) {
        item = makdatum(pagbuf, i);
        if(item.dptr == NULL)
            break;
        if(cmpdatum(key, item) <= 0)
            continue;
        if(f || cmpdatum(bitem, item) < 0) {
            bitem = item;
            f = 0;
        }
    }
    if(f == 0)
        return(bitem);
    hash = hashinc(hash);
    if(hash == 0)
        return(item);
    return(firsthash(hash));
}

/*
 * Return the first 
 */
datum
firsthash(hash)
long hash;
{
    register i;
    datum item, bitem;

loop:
    /* Read first bulk with associated bitno as 0 into pagbuf.
       Values of hmask, blkno and bitno is changed here */
    dbm_access(hash);

    bitem = makdatum(pagbuf, 0); /* first item in pagbuf */

    for(i=2;; i+=2) {
        item = makdatum(pagbuf, i);
        if(item.dptr == NULL)
            break;
        if(cmpdatum(bitem, item) < 0)
            bitem = item;
    }

    if(bitem.dptr != NULL)
        return(bitem);

    /* Increase the hash value.
       hmask is used to calculate hash increase */
    hash = hashinc(hash);
    if(hash == 0)
        return(item);
    goto loop;
}

/*
 * Find the correct block for the given hash.
 * Read the block into pagbuf.
 * Changes the value of hmask, blkno and bitno
 */
dbm_access(hash)
long hash;
{
    static long oldb = -1;

    for(hmask=0;; hmask=(hmask<<1)+1) {
        blkno = hash & hmask;
        bitno = blkno + hmask;
        if(getbit() == 0)
            break;
    }
    if(blkno != oldb) {
        clrbuf(pagbuf, PBLKSIZ);
        lseek(pagf, blkno*PBLKSIZ, 0);
        read(pagf, pagbuf, PBLKSIZ);
        chkblk(pagbuf);
        oldb = blkno;
    }
}

/*
 * Return value of bitno in dir file
 * Return 0 if bitno is out of bounds
 */
getbit()
{
    long bn;
    register b, i, n;
    static oldb = -1;

    if(bitno > maxbno)
        return(0);
    n = bitno % BYTESIZ;  /* bit position inside byte */
    bn = bitno / BYTESIZ; /* position in bytes */
    i = bn % DBLKSIZ;     /* offset inside bulk */
    b = bn / DBLKSIZ;     /* bulk position */
    if(b != oldb) {
        clrbuf(dirbuf, DBLKSIZ);
        lseek(dirf, (long)b*DBLKSIZ, 0);
        read(dirf, dirbuf, DBLKSIZ);
        oldb = b;
    }
    if(dirbuf[i] & (1<<n))
        return(1);
    return(0);
}

/*
 * Sets bitno to 1 in dir file.
 */
setbit()
{
    long bn;
    register i, n, b;

    if(bitno > maxbno) {
        maxbno = bitno;
        getbit();
    }
    n = bitno % BYTESIZ;  /* bit position inside byte */
    bn = bitno / BYTESIZ; /* position in bytes */
    i = bn % DBLKSIZ;     /* offset inside bulk */
    b = bn / DBLKSIZ;     /* bulk position */
    dirbuf[i] |= 1<<n;
    lseek(dirf, (long)b*DBLKSIZ, 0);
    write(dirf, dirbuf, DBLKSIZ);
}

/*
 * Write 0's to entire buffer.
 */
clrbuf(cp, n)
register char *cp;
register n;
{

    do
        *cp++ = 0;
    while(--n);
}

/*
 * Return a datum for the n'th data entry in buf.
 * If the n'th entry doesn't exist data pointer is NULL.
 */
datum
makdatum(buf, n)
char buf[PBLKSIZ];
{
    register short *sp;
    register t;
    datum item;

    sp = (short *)buf;
    if(n < 0 || n >= sp[0])
        goto null;
    t = PBLKSIZ;
    if(n > 0)
        t = sp[n+1-1];
    item.dptr = buf+sp[n+1];
    item.dsize = t - sp[n+1];
    return(item);

null:
    item.dptr = NULL;
    item.dsize = 0;
    return(item);
}

/*
 * Compare equality of datums.
 * 0 is equal.
 * Negative means d1.dsize < d2.dsize or that for the first
 * inequal element d1.dptr[n] < d2.dptr[n]
 */
cmpdatum(d1, d2)
datum d1, d2;
{
    register n;
    register char *p1, *p2;

    n = d1.dsize;
    if(n != d2.dsize)
        return(n - d2.dsize);
    if(n == 0)
        return(0);
    p1 = d1.dptr;
    p2 = d2.dptr;
    do
        if(*p1++ != *p2++)
            return(*--p1 - *--p2);
    while(--n);
    return(0);
}

int hitab[16] = 
{   61, 57, 53, 49, 45, 41, 37, 33,
    29, 25, 21, 17, 13,  9,  5,  1,
};
long    hltab[64] = 
{
    06100151277L,06106161736L,06452611562L,05001724107L,
    02614772546L,04120731531L,04665262210L,07347467531L,
    06735253126L,06042345173L,03072226605L,01464164730L,
    03247435524L,07652510057L,01546775256L,05714532133L,
    06173260402L,07517101630L,02431460343L,01743245566L,
    00261675137L,02433103631L,03421772437L,04447707466L,
    04435620103L,03757017115L,03641531772L,06767633246L,
    02673230344L,00260612216L,04133454451L,00615531516L,
    06137717526L,02574116560L,02304023373L,07061702261L,
    05153031405L,05322056705L,07401116734L,06552375715L,
    06165233473L,05311063631L,01212221723L,01052267235L,
    06000615237L,01075222665L,06330216006L,04402355630L,
    01451177262L,02000133436L,06025467062L,07121076461L,
    03123433522L,01010635225L,01716177066L,05161746527L,
    01736635071L,06243505026L,03637211610L,01756474365L,
    04723077174L,03642763134L,05750130273L,03655541561L,
};

/*
 * Calculate next hash value.
 * Relies on current value of hmask for calculation.
 * Returns 0 when `hash & hmask` is all 1's.
 */
long
hashinc(hash)
long hash;
{
    long bit;

    hash &= hmask;
    bit = hmask+1;
    for(;;) {
        bit >>= 1;
        if(bit == 0)
            return(0L);
        if((hash&bit) == 0)
            return(hash|bit);
        hash &= ~bit;
    }
}

/*
 * Calculate a hash from datum content.
 */
long
calchash(item)
datum item;
{
    register i, j, f;
    long hashl;
    int hashi;

    hashl = 0;
    hashi = 0;
    for(i=0; i<item.dsize; i++) {
        f = item.dptr[i];
        for(j=0; j<BYTESIZ; j+=4) {
            hashi += hitab[f&017];
            hashl += hltab[hashi&077];
            f >>= 4;
        }
    }
    return(hashl);
}

/*
 * Delete n'th item from the buffer.
 * Buffer is reordered to avoid fragmentation.
 */
delitem(buf, n)
char buf[PBLKSIZ];
{
    register short *sp;
    register i1, i2, i3;

    sp = (short *)buf;
    if(n < 0 || n >= sp[0])
        goto bad;
    i1 = sp[n+1]; /* beginning of item to delete */
    i2 = PBLKSIZ; /* end of item to delete */
    if(n > 0)
        i2 = sp[n+1-1];
    i3 = sp[sp[0]+1-1]; /* index of newest element */

    /* move data backwards to ovewrite the data to remove */
    if(i2 > i1)
        while(i1 > i3) {
            i1--;
            i2--;
            buf[i2] = buf[i1];
            buf[i1] = 0;
        }

    /* update indices of data elements */
    i2 -= i1;
    for(i1=n+1; i1<sp[0]; i1++)
        sp[i1+1-1] = sp[i1+1] + i2;
    sp[0]--;
    sp[sp[0]+1] = 0;
    return;

bad:
    printf("bad delitem\n");
    abort();
}

/*
 * Fill the buffer with data from given datum.
 */
additem(buf, item)
char buf[PBLKSIZ];
datum item;
{
    register short *sp;
    register i1, i2;

    sp = (short *)buf;

    /* i1 points to end of data in buffer */
    i1 = PBLKSIZ;
    if(sp[0] > 0)
        i1 = sp[sp[0]+1-1];

    i1 -= item.dsize; /* i1 points to the beginning of data location in buffer */

    /* check that index area don't collide with data area */
    i2 = (sp[0]+2) * sizeof(short);
    if(i1 <= i2)
        return(-1);

    sp[sp[0]+1] = i1; /* add index of current data block to beginning of buffer */

    for(i2=0; i2<item.dsize; i2++) {
        buf[i1] = item.dptr[i2];
        i1++;
    }

    sp[0]++; /* increase index of newest index of data indices */
    return(sp[0]-1); /* return the buffer index of the added data */
}

/*
 * Check validity of buffer.
 * Checks index values and overlap of index and data area.
 */
chkblk(buf)
char buf[PBLKSIZ];
{
    register short *sp;
    register t, i;

    sp = (short *)buf;
    t = PBLKSIZ;

    /* check that indices are correctly ordered and not out of bounds */
    for(i=0; i<sp[0]; i++) {
        if(sp[i+1] > t)
            goto bad;
        t = sp[i+1];
    }

    /* check that index area is not overlapping with data area */
    if(t < (sp[0]+1)*sizeof(short))
        goto bad;

    return;

bad:
    printf("bad block\n");
    abort();
    clrbuf(buf, PBLKSIZ);
}