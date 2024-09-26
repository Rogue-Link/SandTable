//
// Created by chengqian on 24-7-5.
//
#include "common.h"
#include "myopen.h"
#include <fcntl.h> 
#include <stdarg.h>
#include <unistd.h>
#include <stdio.h>
#include "myfread.h"
#include "myMap.h"
#include "router.h"

extern int io_flag;

MAKE_LIB_TEMPLATE(size_t, fread, void *ptr, size_t size, size_t nmemb, FILE *stream) {
    if (!real_fread) {
        real_fread = (size_t (*)(void *ptr, size_t size, size_t nmemb, FILE *stream))dlsym(RTLD_NEXT, "fread");
    }
    size_t ret = real_fread(ptr, size, nmemb, stream);
    int fd = fileno(stream);
    long count = (long)(size * nmemb);
    char *path = map_search(fd);
    LOG_INTERCEPTED(LIB_fread, "fread from file: %s, return %d, read(fd: %d, buf: %p, count: %ld)",
                        path, (long)ret, fd, &ptr, count);
    free(path);
    if (io_flag == -1){
        return -1;
    }
    else if(io_flag == 0) return ret;
    else {
        usleep(io_flag * 1000);
        return ret;
    }
}