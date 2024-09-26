//
// Created by chengqina on 24-7-6.
//

#ifndef MYSYSCALL_MYWRITE_H
#define MYSYSCALL_MYWRITE_H

#include <sys/types.h>
#include <stdio.h>

size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);

#endif //MYSYSCALL_MYWRITE_H
