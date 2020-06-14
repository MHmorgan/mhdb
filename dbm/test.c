/*
 * Source: https://github.com/qpfiffer/Unix-v7-DBM
 */

#include "dbm.h"
#include <stdio.h>
#include <string.h>
#include <err.h>

int idx(char* s, char* sub);

int
main(int argc, char *argv[])
{
    int cmp, ret, i;
    char *sp;
    #define CMDSIZ 4
    char cmd[CMDSIZ] = {0};
    char inp[PBLKSIZ];
    char keybuf[PBLKSIZ], valbuf[PBLKSIZ];
    char dbname[] = "database";
    datum key, val;
    long hash, l;

    printf("Initialize database: \"%s\"\n", dbname);
    if (dbminit(dbname) != 0)
        err(1, "failed to open %s", dbname);

    puts("Type \"hlp\" for a help message");

    do {
        printf("dbm> ");
        memset(inp, 0, PBLKSIZ);
        if (!gets(inp))
            err(1, "gets failed");
        strncpy(cmd, inp, 3);
        cmp = idx("extaddgetdelkeyvalrstclrhlpshwhshblkfstnxtbit", cmd);
        sp = inp+CMDSIZ;

        switch (cmp) {
        case 0: break;

        case 3: /* add */
            printf("(Add {\"%s\" : \"%s\"})\n", key.dptr, val.dptr);
            store(key, val);
            break;

        case 6: /* get */
            printf("(Get \"%s\")\n", key.dptr);
            val.dptr = NULL;
            val.dsize = -1;
            val = fetch(key);
            printf("%s (size %d)\n", val.dptr, val.dsize);
            break;

        case 9: /* del */
            printf("(Delete \"%s\")\n", key.dptr);
            ret = delete(key);
            printf("%d\n", ret);
            break;

        case 12: /* key */
            memset(keybuf, 0, PBLKSIZ);
            strncpy(keybuf, sp, PBLKSIZ);
            key.dptr = keybuf;
            key.dsize = strlen(key.dptr);
            printf("%s (size %d)\n", key.dptr, key.dsize);
            break;

        case 15: /* val */
            memset(valbuf, 0, PBLKSIZ);
            strncpy(valbuf, sp, PBLKSIZ);
            val.dptr = valbuf;
            val.dsize = strlen(val.dptr);
            printf("%s (size %d)\n", val.dptr, val.dsize);
            break;

        case 18: /* rst */
        case 21: /* clr */
            memset(keybuf, 0, PBLKSIZ);
            memset(valbuf, 0, PBLKSIZ);
            key.dptr = NULL;
            key.dsize = -1;
            val.dptr = NULL;
            val.dsize = -1;
            break;

        case 24: /* hlp */
            puts("Commands:\n\
\text - exit\n\
\tadd - add current key-val to database\n\
\tget - get the val of current key\n\
\tdel - delete current key\n\
\tkey - set current key\n\
\tval - set current val\n\
\trst - same as clr\n\
\tclr - clear current key and val\n\
\tshw - show current key and val\n\
\thsh - calculate hash of current key and val\n\
\tblk - get bulkno of current key (calls forder)\n\
\tfst - get first key\n\
\tnxt - get next key (from current key)\n\
\tbit - print bitno and bit value of bitno\n\
\thlp - print this help message");
            break;

        case 27: /* shw */
            printf("Key (size %d): %s\nVal (size %d): %s\n",
                   key.dsize, key.dptr, val.dsize, val.dptr);
            break;

        case 30: /* hsh */
            hash = calchash(key);
            printf("Key: %lx\n", hash);
            for (i = 0; i < key.dsize; i++)
                printf("%d ", key.dptr[i]);
            puts("");
            hash = calchash(val);
            printf("Val: %lx\n", hash);
            for (i = 0; i < val.dsize; i++)
                printf("%d ", val.dptr[i]);
            puts("");
            break;

        case 33: /* blk */
            printf("(forder \"%s\")\n", key.dptr);
            l = forder(key);
            printf("0x%lx\n", l);
            break;

        case 36: /* fst */
            memset(keybuf, 0, PBLKSIZ);
            key.dptr = NULL;
            key.dsize = -1;
            key = firstkey();
            printf("%s (size %d)\n", key.dptr, key.dsize);
            break;

        case 39: /* nxt */
            key = nextkey(key);
            printf("%s (size %d)\n", key.dptr, key.dsize);
            break;

        case 42: /* bit */
            printf("bitno %ld\t%s\n", bitno, getbit() ? "1" : "0");
            break;

        default:
            printf("Unknown command (%d)\n", cmp);
        }

    } while (strncmp(inp, "ext", 3));
    
    puts("Goodbye");
    close(pagf);
    close(dirf);
    return 0;
}

int
idx(char* s, char* sub)
{
    int i, len = strlen(sub);
    char *p1 = s;

    do {
        if (*p1 == *sub) {
            for (i = 1; i < len; i++)
                if (p1[i] != sub[i])
                    break;
            if (i == len)
                return p1 - s;
        }
    } while (*++p1 != 0);

    return -1;
}