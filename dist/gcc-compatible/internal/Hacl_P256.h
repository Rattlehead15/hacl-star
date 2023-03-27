/* MIT License
 *
 * Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
 * Copyright (c) 2022-2023 HACL* Contributors
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#ifndef __internal_Hacl_P256_H
#define __internal_Hacl_P256_H

#if defined(__cplusplus)
extern "C" {
#endif

#include <string.h>
#include "krml/internal/types.h"
#include "krml/lowstar_endianness.h"
#include "krml/internal/target.h"

#include "internal/Hacl_Krmllib.h"
#include "internal/Hacl_Bignum_Base.h"
#include "../Hacl_P256.h"
#include "lib_intrinsics.h"

void Hacl_Impl_P256_Bignum_bn_mul4(uint64_t *res, uint64_t *x, uint64_t *y);

void Hacl_Impl_P256_Field_fmul(uint64_t *res, uint64_t *x, uint64_t *y);

void Hacl_Impl_P256_SolinasReduction_solinas_reduction_impl(uint64_t *i, uint64_t *o);

uint64_t Hacl_Impl_P256_Point_is_point_at_inf(uint64_t *p);

void Hacl_Impl_P256_Point_aff_point_store(uint8_t *res, uint64_t *p);

bool Hacl_Impl_P256_Point_load_point_vartime(uint64_t *p, uint8_t *b);

void Hacl_Impl_P256_PointMul_point_mul_bytes(uint64_t *res, uint64_t *p, uint8_t *scalar);

void Hacl_Impl_P256_PointMul_point_mul_g_bytes(uint64_t *res, uint8_t *scalar);

#if defined(__cplusplus)
}
#endif

#define __internal_Hacl_P256_H_DEFINED
#endif
