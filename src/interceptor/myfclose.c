//
// Created by chengqian on 24-7-7.
//
#include "common.h"
#include "myclose.h"
#include "config.h"
#include <stdio.h>
#include "myMap.h"


MAKE_LIB_TEMPLATE(int, fclose, FILE *stream) {
    if (!real_fclose) {
        real_fclose =(int (*)(FILE*))dlsym(RTLD_NEXT, "fclose");
    }
    int fd = fileno(stream); 
    const char *path = map_search(fd);
    map_delete(fd);
    int ret = real_fclose(stream); 
    LOG_INTERCEPTED(LIB_fclose, "fclose file: %s, return %d, close(fd: %d)", path, ret, fd);    
    return ret;
}
