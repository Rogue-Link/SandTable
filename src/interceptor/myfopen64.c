//
// Created by chengqian on 24-7-5.
//
#include "common.h"
#include "myopen.h"
#include <fcntl.h> 
#include <stdarg.h>
#include <stdio.h>
#include "myMap.h"

MAKE_LIB_TEMPLATE(FILE*, fopen64, const char *pathname, const char *mode) {
    if (!real_fopen64) {
        real_fopen64 = (FILE *(*)(const char *pathname, const char *mode))dlsym(RTLD_NEXT, "fopen");
    }
    FILE *ret;
    ret = real_fopen64(pathname, mode);
    int fd = fileno(ret);
    map_insert(fd, pathname);
    LOG_INTERCEPTED(LIB_fopen64, "fopen64 return fd: %d, fopen(pathname: \"%s\", mode: %04o)",
                 fd, rstr1(pathname), mode);
    return ret; 
}
