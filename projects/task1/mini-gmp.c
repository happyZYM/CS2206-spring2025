#include "mini-gmp.h"

mp_size_t gmp_abs(mp_size_t x) {
  return x >= 0 ? x : -x;
}

mp_size_t gmp_max(mp_size_t a, mp_size_t b) {
  return a > b ? a : b;
}

int gmp_cmp(mp_size_t a, mp_size_t b) {
  return (a > b) - (a < b);
}

/* MPN interface */

/* 从 低地址向高地址 顺序复制 */
void
mpn_copyi (mp_ptr d, mp_srcptr s, mp_size_t n)
{
  mp_size_t i;
  for (i = 0; i < n; i++)
    d[i] = s[i];
}

/* 大于返回1，小于返回-1，等于返回0 */
int
mpn_cmp (mp_srcptr ap, mp_srcptr bp, mp_size_t n)
{
  while (--n >= 0)
    {
      if (ap[n] != bp[n])
	return ap[n] > bp[n] ? 1 : -1;
    }
  return 0;
}

/*处理位数不同的情况*/
static int
mpn_cmp4 (mp_srcptr ap, mp_size_t an, mp_srcptr bp, mp_size_t bn)
{
  if (an != bn)
    return an < bn ? -1 : 1;
  else
    return mpn_cmp (ap, bp, an);
}

/*返回非0的位数*/
static mp_size_t
mpn_normalized_size (mp_srcptr xp, mp_size_t n)
{
  while (n > 0 && xp[n-1] == 0)
    --n;
  return n;
}

/* 多精度数ap 加上单精度数b，返回最后产生的进位 */
mp_limb_t
mpn_add_1 (mp_ptr rp, mp_srcptr ap, mp_size_t n, mp_limb_t b)
{
  mp_size_t i;
  //assert (n > 0);
  i = 0;
  do
    {
      mp_limb_t r = ap[i] + b;
      /* Carry out */
      b = (r < b);
      rp[i] = r;
    }
  while (++i < n);

  return b;
}

/* 位数相同的多精度数ap 加上多精度数bp，返回最后产生的进位 */
mp_limb_t
mpn_add_n (mp_ptr rp, mp_srcptr ap, mp_srcptr bp, mp_size_t n)
{
  mp_size_t i;
  mp_limb_t cy;

  for (i = 0, cy = 0; i < n; i++)
    {
      mp_limb_t a, b, r;
      a = ap[i]; b = bp[i];
      r = a + cy;
      cy = (r < cy);
      r += b;
      cy += (r < b);
      rp[i] = r;
    }
  return cy;
}

/*不同位数的多精度数相加，返回最后的进位*/
mp_limb_t
mpn_add (mp_ptr rp, mp_srcptr ap, mp_size_t an, mp_srcptr bp, mp_size_t bn)
{
  mp_limb_t cy;
  //assert (an >= bn);
  cy = mpn_add_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_add_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}

mp_limb_t
mpn_sub_1 (mp_ptr rp, mp_srcptr ap, mp_size_t n, mp_limb_t b)
{
  mp_size_t i;
  //assert (n > 0);
  i = 0;
  do
    {
      mp_limb_t a = ap[i];
      /* Carry out */
      mp_limb_t cy = a < b;
      rp[i] = a - b;
      b = cy;
    }
  while (++i < n);

  return b;
}

mp_limb_t
mpn_sub_n (mp_ptr rp, mp_srcptr ap, mp_srcptr bp, mp_size_t n)
{
  mp_size_t i;
  mp_limb_t cy;

  for (i = 0, cy = 0; i < n; i++)
    {
      mp_limb_t a, b;
      a = ap[i]; b = bp[i];
      b += cy;
      cy = (b < cy);
      cy += (a < b);
      rp[i] = a - b;
    }
  return cy;
}

mp_limb_t
mpn_sub (mp_ptr rp, mp_srcptr ap, mp_size_t an, mp_srcptr bp, mp_size_t bn)
{
  mp_limb_t cy;
  //assert (an >= bn);
  cy = mpn_sub_n (rp, ap, bp, bn);
  if (an > bn)
    cy = mpn_sub_1 (rp + bn, ap + bn, an - bn, cy);
  return cy;
}

/* MPZ interface */

void
mpz_clear (mpz_t r)
{
  if (r->_mp_alloc)
    gmp_free_limbs (r->_mp_d, r->_mp_alloc);
}

static mp_ptr
mpz_realloc (mpz_t r, mp_size_t size)
{
  size = gmp_max (size, 1);

  if (r->_mp_alloc)
    r->_mp_d = gmp_realloc_limbs (r->_mp_d, r->_mp_alloc, size);
  else
    r->_mp_d = gmp_alloc_limbs (size);
  r->_mp_alloc = size;

  if (gmp_abs (r->_mp_size) > size)
    r->_mp_size = 0;

  return r->_mp_d;
}

/* Realloc for an mpz_t WHAT if it has less than NEEDED limbs.  */
mp_ptr mrz_realloc_if(mpz_t z,mp_size_t n) {
  return n > z->_mp_alloc ? mpz_realloc(z, n) : z->_mp_d;
}

/* MPZ comparisons and the like. */
int
mpz_sgn (const mpz_t u)
{
  return gmp_cmp (u->_mp_size, 0);
}

void
mpz_swap (mpz_t u, mpz_t v)
{
  mp_size_t_swap (u->_mp_alloc, v->_mp_alloc);
  mp_ptr_swap(u->_mp_d, v->_mp_d);
  mp_size_t_swap (u->_mp_size, v->_mp_size);
}

/* MPZ addition and subtraction */

static mp_size_t
mpz_abs_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  mp_size_t an = gmp_abs (a->_mp_size);
  mp_size_t bn = gmp_abs (b->_mp_size);
  mp_ptr rp;
  mp_limb_t cy;

  if (an < bn)
    {
      mpz_srcptr_swap (a, b);
      mp_size_t_swap (an, bn);
    }

  rp = mrz_realloc_if (r, an + 1);
  cy = mpn_add (rp, a->_mp_d, an, b->_mp_d, bn);

  rp[an] = cy;

  return an + cy;
}

static mp_size_t
mpz_abs_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  mp_size_t an = gmp_abs (a->_mp_size);
  mp_size_t bn = gmp_abs (b->_mp_size);
  int cmp;
  mp_ptr rp;

  cmp = mpn_cmp4 (a->_mp_d, an, b->_mp_d, bn);
  if (cmp > 0)
    {
      rp = mrz_realloc_if (r, an);
      mpn_sub (rp, a->_mp_d, an, b->_mp_d, bn);
      return mpn_normalized_size (rp, an);
    }
  else if (cmp < 0)
    {
      rp = mrz_realloc_if (r, bn);
      mpn_sub (rp, b->_mp_d, bn, a->_mp_d, an);
      return -mpn_normalized_size (rp, bn);
    }
  else
    return 0;
}

void
mpz_add (mpz_t r, const mpz_t a, const mpz_t b)
{
  mp_size_t rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_add (r, a, b);
  else
    rn = mpz_abs_sub (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}

void
mpz_sub (mpz_t r, const mpz_t a, const mpz_t b)
{
  mp_size_t rn;

  if ( (a->_mp_size ^ b->_mp_size) >= 0)
    rn = mpz_abs_sub (r, a, b);
  else
    rn = mpz_abs_add (r, a, b);

  r->_mp_size = a->_mp_size >= 0 ? rn : - rn;
}
