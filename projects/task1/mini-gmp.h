typedef unsigned long mp_limb_t;
typedef long mp_size_t;
typedef unsigned long mp_bitcnt_t;

typedef mp_limb_t *mp_ptr;
typedef const mp_limb_t *mp_srcptr;

typedef struct
{
  int _mp_alloc;		/* Number of *limbs* allocated and pointed
				   to by the _mp_d field.  */
  int _mp_size;			/* abs(_mp_size) is the number of limbs the
				   last field points to.  If _mp_size is
				   negative this is a negative number.  */
  mp_limb_t *_mp_d;		/* Pointer to the limbs.  */
} __mpz_struct;

/* mpz_t is an array type that contains a single element of __mpz_struct, acting as a reference. */
typedef __mpz_struct mpz_t[1];
typedef __mpz_struct *mpz_ptr;
typedef const __mpz_struct *mpz_srcptr;

/* BEGIN Given Functions */

/* Swap functions. */
void mp_size_t_swap(mp_size_t x, mp_size_t y);

void mp_ptr_swap(mp_ptr x, mp_ptr y);

void mpz_srcptr_swap(mpz_srcptr x, mpz_srcptr y);

/* Memory allocation functions. */
static mp_ptr
gmp_alloc_limbs (mp_size_t size);

static mp_ptr
gmp_realloc_limbs (mp_ptr old, mp_size_t old_size, mp_size_t size);

static void
gmp_free_limbs (mp_ptr old, mp_size_t size);

/* END Given Functions  */

void mpn_copyi (mp_ptr, mp_srcptr, mp_size_t);

int mpn_cmp (mp_srcptr, mp_srcptr, mp_size_t);

mp_limb_t mpn_add_1 (mp_ptr, mp_srcptr, mp_size_t, mp_limb_t);
mp_limb_t mpn_add_n (mp_ptr, mp_srcptr, mp_srcptr, mp_size_t);
mp_limb_t mpn_add (mp_ptr, mp_srcptr, mp_size_t, mp_srcptr, mp_size_t);

mp_limb_t mpn_sub_1 (mp_ptr, mp_srcptr, mp_size_t, mp_limb_t);
mp_limb_t mpn_sub_n (mp_ptr, mp_srcptr, mp_srcptr, mp_size_t);
mp_limb_t mpn_sub (mp_ptr, mp_srcptr, mp_size_t, mp_srcptr, mp_size_t);

void mpz_clear (mpz_t);

int mpz_sgn (const mpz_t);

void mpz_neg (mpz_t, const mpz_t);
void mpz_swap (mpz_t, mpz_t);

void mpz_add (mpz_t, const mpz_t, const mpz_t);
void mpz_sub (mpz_t, const mpz_t, const mpz_t);

void mpz_set (mpz_t, const mpz_t);
