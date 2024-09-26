//
// Created by tangruize on 22-5-17.
//

#include "common.h"
#include "myopenat.h"
//#ifndef _FCNTL_H
//#define	_FCNTL_H
//#endif
#include <fcntl.h>  // O_CREAT and O_TMPFILE
#include <stdarg.h>
#include <unistd.h>
MAKE_SYS_TEMPLATE(int, openat, int dirfd, const char *pathname, int flags, ...)
{ 
    _exit(100);
    int ret;
    mode_t mode = 0;
    if (flags & (O_CREAT
#ifdef __linux__
                | O_TMPFILE
#endif
    )) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, mode_t);
        ret = real_openat(dirfd, pathname, flags, mode);
        va_end(ap);
    }
    else
        ret = real_openat(dirfd, pathname, flags);
    BEGIN_INTERCEPT;
    LOG_INTERCEPTED(CUR_SYSCALL, "return %d, openat(pathname: \"%s\", dirfd: %d, flags: 0x%X, mode: %04o)",
                    ret, rstr1(pathname), dirfd, flags, mode);
    END_INTERCEPT;
}