/*
  Author:  Pate Williams (c) 1997 & James Wanless (c) 2008

  Multiple precision Goldwasser-Kilian primality test.
  See "A Course in Computational Algebraic Number
  Theory" by Henri Cohen Algorithm 9.2.3 page 470.
*/

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include <iostream.h>
#include <gmpxx.h>
#include <gmp.h>


#define SIEVE_LIMIT 1024

struct point {mpz_class x, y;};

mpz_class gcd(mpz_class a, mpz_class b)
/* returns greatest common divisor of a and b */
{
  mpz_t temp;
  mpz_init(temp);
  mpz_gcd(temp, a.get_mpz_t(), b.get_mpz_t());
  mpz_class temp_class(temp);
  mpz_clear(temp);
  return temp_class;
}

void Euclid_extended(mpz_class a, mpz_class b, mpz_class *u, mpz_class *v, mpz_class *d)
{
  mpz_class q, t1, t3, v1, v3;

  *u = 1, *d = a;
  if (b == 0) {
    *v = 0;
    return;
  }
  v1 = 0, v3 = b;
  while (v3 != 0) {
    q = *d / v3;
    t3 = *d - q * v3;
    t1 = *u - q * v1;
    *u = v1, *d = v3;
    v1 = t1, v3 = t3;
  }
  *v = (*d - a * *u) / b;
}

mpz_class inverse(mpz_class a, mpz_class b)
/* returns inverse of a modulo b or 0 if it does not exist */
{
  mpz_class d, u, v;

  Euclid_extended(a, b, &u, &v, &d);
  if (d == 1) return u;
  return 0;
}

int addition_1(mpz_class n, struct point P1, struct point P2, struct point *P3)
/* returns 1 if P1 = -P2 therefore P1 + P2 = O, 0 otherwise */
/* P1 != P2 */
{
  mpz_class delta_x = (P2.x - P1.x) % n;
  mpz_class delta_y = (P2.y - P1.y) % n;
  mpz_class m;

  if (P1.x == P2.x && P1.y == - P2.y) {
    P3->x = 0, P3->y = 1;
    return 1;
  }
  /* calculate m = (y2 - y1)(x2 - x1) ^ -1 mod n */
  if (delta_x < 0) delta_x += n;
  if (delta_y < 0) delta_y += n;
  m = delta_y * inverse(delta_x, n) % n;
  /* calculate x3 = m ^ 2 - (x1 + x2) mod n */
  P3->x = (m * m - (P1.x + P2.x)) % n;
  /* calculate y3 = m(x1 - x3) - y1 mod n */
  P3->y = (m * (P1.x - P3->x) - P1.y) % n;
  return 0;
}

void addition_2(mpz_class a, mpz_class n, struct point P1, struct point *P3)
/* P1 == P2 */
{
  mpz_class m;

  /* calculate m = (3x1 ^ 2 + a)(2y1) ^ -1 mod n */
  m = (3 * P1.x * P1.x + a) * inverse(2 * P1.y, n) % n;
  /* calculate x3 = m ^ 2 - 2x1 mod n */
  P3->x = (m * m - 2 * P1.x) % n;
  /* calculate y3 = m(x1 - x3) - y1 mod n */
  P3->y = (m * (P1.x - P3->x) - P1.y) % n;
}

int multiply(mpz_class a, mpz_class k, mpz_class n, struct point P, struct point *R, mpz_class *d)
/* returns -1 if O encountered, 0 if divisor not found, 1 otherwise */
{
  int value = 1;
  struct point A, B, C;

  /*  A = P */
  A = P;
  /* B = O = (0, 1) the point at infinity */
  B.x = 0, B.y = 1;
  while (value && k > 0) {
    if (k % 2 == 1) {
      *d = gcd((B.x - A.x) % n, n);
      k--;
      value = *d == 1 || *d == n;
      if (A.x == 0 && A.y == 1);
      else if (B.x == 0 && B.y == 1) B = A;
      else if (value) {
        addition_1(n, A, B, &C);
        B = C;
      }
    }
    else {
      *d = gcd((2 * A.y) % n, n);
      k >>= 1;
      value = *d == 1 || *d == n;
      if (value) {
        addition_2(a, n, A, &C);
        A = C;
      }
    }
  }
  *R = B;
  if (R->x < 0) R->x += n;
  if (R->y < 0) R->y += n;
  if (R->x == 0 && R->y == 1) return -1;
  return !value;
}

int JACOBI(mpz_class a, mpz_class b)
{
    return mpz_jacobi(a.get_mpz_t(), b.get_mpz_t());
}

mpz_class exp_mod(mpz_class x, mpz_class b, mpz_class n)
/* returns x ^ b mod n */
{
  mpz_t temp;
  mpz_init (temp);
  mpz_powm(temp, x.get_mpz_t(), b.get_mpz_t(), n.get_mpz_t());
  mpz_class temp_class(temp);
  mpz_clear (temp);
  return temp_class;
}

int Rabin_Miller(mpz_class n)
/* given an integer n >= 3 returns 0 composite, 1 probably prime */
{
  return mpz_probab_prime_p(n.get_mpz_t(), 10);
}

mpz_class cardinality(mpz_class a, mpz_class b, mpz_class p)
/* returns the cardinality of the elliptic curve
   E(F_p): y ^ 2 = x ^ 3 + ax + b using
   |E(F_p)| = p + 1 - a_p
   a_p = -sum(0 <= x < p, (y ^ 2 / p)) */
{
  mpz_class a_p = 0, x;

  for (x = 0; x < p; x++)
    a_p += JACOBI((((x * x) % p * x) % p + a * x + b) % p, p);
  return p + 1 + a_p;
}

mpz_class square_root_mod(mpz_class a, mpz_class p)
/* returns square root of a modulo p if it exists, 0 otherwise */
{
  mpz_class b, e = 0, m, n, q = p - 1, r, t, x, y, z;
  mpz_class TWO = 2;

  /* p - 1 = 2 ^ e * q with q odd */
  while (q % 2 == 0) q >>= 1, e++;
  /* find generator */
  do
    do n = rand() % p; while (p == 0);
  while (JACOBI(n, p) != -1);
  z = exp_mod(n, q, p);
  y = z, r = e;
  x = exp_mod(a, (q - 1) / 2, p);
  b = ((a * x % p) * x) % p;
  x = (a * x) % p;
  do {
  if (b == 1) return x;
  m = 1;
  while (exp_mod(b, TWO ^ m, p) != 1) m++;
  if (m == r) return 0;
  t = exp_mod(y, TWO ^ (r - m - 1), p);
  y = t * t % p;
  r = m;
  x = x * t % p;
  b = b * y % p;
  } while (true);
}

int Goldwasser_Kilian(mpz_class N)
/* returns 0 if N is composite, 1 if prime */
{
  int value1, value2;
  long p;
  mpz_class Ni = N, a, b, d, i = 0, m, q, t, x, y;
  struct point P, P1, P2;

  do {
  
  if (Ni <= SIEVE_LIMIT) {
    p = 2;
    while (p <= sqrt(Ni)) {
      if (Ni % p == 0) {
        cout << "1 factor = " << p << "\n";
        return 0;
      }
      p++;
    }
    return 1;
  }
  if (!Rabin_Miller(Ni)) return 0;
  
  do {
  do {
    do a = rand() % Ni; while (a == 0);
    do b = rand() % Ni; while (b == 0);
    m = (4 * a * a * a + 27 * b * b) % Ni;
  } while (m == 0);
  m = cardinality(a, b, Ni);
  q = m / 2;
  t = sqrt(sqrt(Ni)) + 1;
  } while ((m % 2 == 1) || !Rabin_Miller(q) || q <= t * t);
  
  do {
  do {
  do {
    do x = rand() % Ni; while (x == 0);
    y = (((x * x) % Ni * x) % Ni + a * x + b) % Ni;
  } while (JACOBI(y, Ni) == -1);
  y = square_root_mod(y, Ni);
  } while (y == 0);
  P.x = x, P.y = y;
  value1 = multiply(a, m, Ni, P, &P1, &d);
  if (value1 == 1) {
    cout << "2 factor = " << d << "\n";
    return 0;
  }
  value2 = multiply(a, 2, Ni, P, &P2, &d);
  if (value2 == 1) {
    cout << "3 factor = " << d << "\n";
    return 0;
  }
  } while (value1 == -1 || value2 == -1);
  
  cout << "N[" << i << "] = " << Ni << "\n";
  cout << "a = " << a << "\n";
  cout << "b = " << b << "\n";
  cout << "m = " << m << "\n";
  cout << "q = " << q << "\n";
  cout << "P = (" << P.x << ", " << P.y << ")\n";
  cout << "P1 = (" << P1.x << ", " << P1.y << ")\n";
  cout << "P2 = (" << P2.x << ", " << P2.y << ")\n";
  i++;
  Ni = q;
  } while (true);
}


int main(void)
{
  mpz_class N;

  for (;;) {
    cout << "number to be tested or 0 to quit:\n";
    cin >> N;
    if (N == 0) break;
    if (Goldwasser_Kilian(N))
      cout << ("proven prime\n");
    else
      cout << ("composite\n");
  }
  return 0;
}
