//
// Created by chengqian on 24-7-5.
//

#include "common.h"
#include "myopen.h"

//#ifndef _FCNTL_H
//#define	_FCNTL_H
//#endif
#include <fcntl.h> 
#include <stdarg.h>
#include <stdio.h>
#include "router.h"
#include <unistd.h>


extern int io_flag;

MAKE_LIB_TEMPLATE(size_t, fwrite, const void *ptr, size_t size, size_t nmemb, FILE *stream) {
    size_t ret = real_fwrite(ptr, size, nmemb, stream);
    int fd = fileno(stream);
    long count = (long)(size * nmemb);
    LOG_INTERCEPTED(LIB_fwrite, "fwrite the file, return %d, read(fd: %d, buf: %p, count: %ld)",
                        (long)ret, fd, &ptr, count);
    if (io_flag == -1){
        return -1;
    }
    else if(io_flag == 0) return ret;
    else {
        usleep(io_flag * 1000);
        return ret;
    }
}
