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

MAKE_LIB_TEMPLATE(size_t, fwrite64, const void *ptr, size_t size, size_t nmemb, FILE *stream) {
    return fwrite(ptr, size, nmemb, stream);
}
