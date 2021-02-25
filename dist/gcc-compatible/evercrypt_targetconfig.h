#ifndef __EVERCRYPT_TARGETCONFIG_H
#define __EVERCRYPT_TARGETCONFIG_H

/* References:
 * - https://docs.microsoft.com/en-us/cpp/preprocessor/predefined-macros?view=vs-2017
 * - https://sourceforge.net/p/predef/wiki/Architectures/
 */

/* TODO: this should be overhauled to use the outcome of the configure script,
 * found in config.h, exclusively, rather than doing feature tests via
 * preprocessor macros. In particular, the only relevant information for
 * EverCrypt should be: COMPILE_VEC128 and COMPILE_VEC256. */

#if defined(__x86_64__) || defined(_M_X64)
#define EVERCRYPT_TARGETCONFIG_X64 1
#elif defined(__i386__) || defined(_M_IX86)
#define EVERCRYPT_TARGETCONFIG_X86 1
#elif defined(__aarch64__) || defined(_M_ARM64)
#define EVERCRYPT_TARGETCONFIG_AARCH64 1
#elif defined(__arm__) || defined(_M_ARM)
#define EVERCRYPT_TARGETCONFIG_AARCH32 1
#endif

#if __has_include("config.h")
#include "config.h"
#endif

#if defined(__GNUC__) && defined(SUPPORTS_INLINE_ASM)
#define EVERCRYPT_TARGETCONFIG_GCC 1
#endif

#endif
