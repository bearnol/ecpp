/*
  Author:  Pate Williams (c) 1997 & James Wanless (c) 2008-19 & Chris Studholme (c) 2004
 & Elisavet Konstantinou & Yiannis Stamatiu & Christos Zaroliagis (c) 2003
 & Scott Contini (c) 1996 & Paul Zimmermann (c) 2005 & Timo Poikola (c) 2010

  Multiple precision Atkin primality test.
  See "A Course in Computational Algebraic Number
  Theory" by Henri Cohen Algorithm 9.2.4 page 474.

  Go translation converted from C++.
*/

package main

import (
	"flag"
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"os"
	"runtime"
	"time"
)

const (
	SIEVE_LIMIT = 1073741824
	LOG2        = 0.301029995
	POLY_SIZE   = 8192
	PRECISION   = 10000
	ERROR_SHIFT = 1000
	BMAX        = 2000
	DMAX        = 20
)

var (
	quiet       int
	Quiet       int
	verbose     int
	one         int
	weber       int
	hilbert     int
	threads     int
	seed        int64
	precision   uint
	error_shift int64
	Bmax        int64
	Dmax        int64

	staticBmax bool
	staticDmax bool

	rgen *rand.Rand
)

type Complex struct {
	x, y *big.Float
}

type Point struct {
	x, y *big.Int
}

var (
	PIf                 *big.Float
	Ef                  *big.Float
	NATLOGONEPOINTNINEf *big.Float

	HALF         *big.Float
	ONEPOINTNINE *big.Float

	ZERO                 *big.Float
	ONE                  *big.Float
	TWO                  *big.Float
	THREE                *big.Float
	FOUR                 *big.Float
	FIVE                 *big.Float
	SIX                  *big.Float
	EIGHT                *big.Float
	TEN                  *big.Float
	TWELVE               *big.Float
	EIGHTEEN             *big.Float
	NINETEEN             *big.Float
	TWENTYFOUR           *big.Float
	FIFTYSEVEN           *big.Float
	TWOHUNDREDTHIRTYNINE *big.Float
	TWOHUNDREDFIFTYSIX   *big.Float
)

func newFloat(val float64) *big.Float {
	return new(big.Float).SetPrec(precision).SetFloat64(val)
}

func newInt(val int64) *big.Int {
	return big.NewInt(val)
}

func rand2() *big.Int {
	/* returns pseudo-random number of 32-bits */
	val := rgen.Uint32()
	return big.NewInt(int64(val))
}

func gcd(a, b *big.Int) *big.Int {
	return new(big.Int).GCD(nil, nil, a, b)
}

func inverse(a, b *big.Int) *big.Int {
	res := new(big.Int).ModInverse(a, b)
	if res == nil {
		return big.NewInt(0)
	}
	return res
}

func modpos(a, b *big.Int) *big.Int {
	temp := new(big.Int).Mod(a, b)
	if temp.Sign() < 0 {
		temp.Add(temp, b)
	}
	return temp
}

func expMod(x, b, n *big.Int) *big.Int {
	return new(big.Int).Exp(x, b, n)
}

func expPow(a *big.Int, e uint64) *big.Int {
	return new(big.Int).Exp(a, big.NewInt(int64(e)), nil)
}

func JACOBI(a, b *big.Int) int {
	return big.Jacobi(a, b)
}

func RabinMiller(n *big.Int) bool {
	return n.ProbablyPrime(10)
}

func squareTest(n *big.Int) (bool, *big.Int) {
	root := new(big.Int).Sqrt(n)
	sq := new(big.Int).Mul(root, root)
	return sq.Cmp(n) == 0, root
}

func cubeTest(n *big.Int) (bool, *big.Int) {
	root := new(big.Int)
	f := new(big.Float).SetInt(n)
	fVal, _ := f.Float64()
	cRoot := math.Cbrt(fVal)
	root.SetInt64(int64(math.Round(cRoot)))

	cube := new(big.Int).Exp(root, big.NewInt(3), nil)
	if cube.Cmp(n) == 0 {
		return true, root
	}
	return false, root
}

func poweroftwoTest(n *big.Int) bool {
	temp := new(big.Int).Abs(n)
	if temp.Sign() == 0 {
		return false
	}
	two := big.NewInt(2)
	rem := new(big.Int)
	for {
		if temp.Cmp(big.NewInt(1)) == 0 {
			return true
		}
		temp, rem = new(big.Int).DivMod(temp, two, rem)
		if rem.Sign() != 0 {
			return false
		}
	}
}

func nextp(n *big.Int) *big.Int {
	p := new(big.Int).Set(n)
	for {
		p.Add(p, big.NewInt(1))
		if p.ProbablyPrime(10) {
			return p
		}
	}
}

func addition1(n *big.Int, P1, P2 Point) (int, Point) {
	var P3 Point
	deltaX := modpos(new(big.Int).Sub(P2.x, P1.x), n)
	deltaY := modpos(new(big.Int).Sub(P2.y, P1.y), n)

	if P1.x.Cmp(P2.x) == 0 && modpos(new(big.Int).Add(P1.y, P2.y), n).Sign() == 0 {
		P3.x = big.NewInt(0)
		P3.y = big.NewInt(1)
		return 1, P3
	}

	invX := inverse(deltaX, n)
	m := modpos(new(big.Int).Mul(deltaY, invX), n)

	m2 := new(big.Int).Mul(m, m)
	x1PlusX2 := new(big.Int).Add(P1.x, P2.x)
	P3.x = modpos(new(big.Int).Sub(m2, x1PlusX2), n)

	x1SubX3 := new(big.Int).Sub(P1.x, P3.x)
	P3.y = modpos(new(big.Int).Sub(new(big.Int).Mul(m, x1SubX3), P1.y), n)

	return 0, P3
}

func addition2(a, n *big.Int, P1 Point) Point {
	var P3 Point
	num := new(big.Int).Mul(big.NewInt(3), new(big.Int).Mul(P1.x, P1.x))
	num.Add(num, a)

	den := new(big.Int).Mul(big.NewInt(2), P1.y)
	m := modpos(new(big.Int).Mul(num, inverse(den, n)), n)

	m2 := new(big.Int).Mul(m, m)
	twoX1 := new(big.Int).Mul(big.NewInt(2), P1.x)
	P3.x = modpos(new(big.Int).Sub(m2, twoX1), n)

	x1SubX3 := new(big.Int).Sub(P1.x, P3.x)
	P3.y = modpos(new(big.Int).Sub(new(big.Int).Mul(m, x1SubX3), P1.y), n)

	return P3
}

func multiply(a, k, n *big.Int, P Point, R *Point, d **big.Int) int {
	value := 1
	var A, B, C Point

	A = P
	B.x = big.NewInt(0)
	B.y = big.NewInt(1)

	kCopy := new(big.Int).Set(k)

	for value != 0 && kCopy.Sign() > 0 {
		if kCopy.Bit(0) != 0 {
			diff := modpos(new(big.Int).Sub(B.x, A.x), n)
			*d = gcd(diff, n)

			kCopy.Sub(kCopy, big.NewInt(1))
			valueBool := (*d).Cmp(big.NewInt(1)) == 0 || (*d).Cmp(n) == 0
			if valueBool {
				value = 1
			} else {
				value = 0
			}

			if A.x.Sign() == 0 && A.y.Cmp(big.NewInt(1)) == 0 {
			} else if B.x.Sign() == 0 && B.y.Cmp(big.NewInt(1)) == 0 {
				B = A
			} else if value != 0 {
				_, C = addition1(n, A, B)
				B = C
			}
		} else {
			twoAy := new(big.Int).Mul(big.NewInt(2), A.y)
			*d = gcd(modpos(twoAy, n), n)

			kCopy.Rsh(kCopy, 1)
			valueBool := (*d).Cmp(big.NewInt(1)) == 0 || (*d).Cmp(n) == 0
			if valueBool {
				value = 1
			} else {
				value = 0
			}

			if value != 0 {
				C = addition2(a, n, A)
				A = C
			}
		}
	}

	*R = B
	R.x = modpos(R.x, n)
	R.y = modpos(R.y, n)

	if R.x.Sign() == 0 && R.y.Cmp(big.NewInt(1)) == 0 {
		return -1
	}

	if value == 0 {
		return 1
	}
	return 0
}

func squareRootMod1(a, p *big.Int) *big.Int {
	e := int64(0)
	q := new(big.Int).Sub(p, big.NewInt(1))
	A := modpos(a, p)

	two := big.NewInt(2)

	for q.Bit(0) == 0 {
		q.Rsh(q, 1)
		e++
	}

	var n *big.Int
	for {
		for {
			n = modpos(rand2(), p)
			if n.Sign() != 0 {
				break
			}
		}
		if JACOBI(n, p) == -1 {
			break
		}
	}

	z := expMod(n, q, p)
	y := new(big.Int).Set(z)
	r := e

	qSub1Div2 := new(big.Int).Div(new(big.Int).Sub(q, big.NewInt(1)), two)
	x := expMod(a, qSub1Div2, p)

	b := modpos(new(big.Int).Mul(new(big.Int).Mul(A, modpos(x, p)), x), p)
	x = modpos(new(big.Int).Mul(A, x), p)

	for {
		if b.Cmp(big.NewInt(1)) == 0 {
			return x
		}

		m := int64(1)
		pow2m := new(big.Int).Lsh(big.NewInt(1), uint(m))
		for expMod(b, pow2m, p).Cmp(big.NewInt(1)) != 0 {
			m++
			pow2m.Lsh(big.NewInt(1), uint(m))
		}

		if m == r {
			return big.NewInt(0)
		}

		powShift := uint(r - m - 1)
		t := expMod(y, new(big.Int).Lsh(big.NewInt(1), powShift), p)
		y = modpos(new(big.Int).Mul(t, t), p)

		r = m
		x = modpos(new(big.Int).Mul(x, t), p)
		b = modpos(new(big.Int).Mul(b, y), p)
	}
}

func mpzSqrtmod(a, p *big.Int) *big.Int {
	s := new(big.Int)
	q := new(big.Int)
	y := new(big.Int)

	if new(big.Int).Mod(p, big.NewInt(4)).Int64() == 3 {
		q.Add(p, big.NewInt(1))
		q.Rsh(q, 2)
		s.Exp(a, q, p)
		y.Mul(s, s).Mod(y, p)
		if y.Cmp(a) != 0 {
			return big.NewInt(0)
		}
		return s
	}

	q.Sub(p, big.NewInt(1))
	var r int64
	if q.Sign() == 0 {
		r = -1
	} else {
		for i := 0; ; i++ {
			if q.Bit(i) == 1 {
				r = int64(i)
				break
			}
		}
		q.Rsh(q, uint(r))
	}

	n := int64(3)
	kronecker := func(pVal, nVal int64) int {
		return JACOBI(big.NewInt(pVal), big.NewInt(nVal))
	}

	var m int
	if (p.Int64()&3) == 3 {
		m = -kronecker(p.Int64(), n)
	} else {
		m = kronecker(p.Int64(), n)
	}

	for m != -1 {
	loop:
		n += 2
		if n%3 == 0 {
			n += 2
		}
		for i := int64(5); i*i <= n; {
			if n%i == 0 {
				goto loop
			}
			i += 2
			if n%i == 0 {
				goto loop
			}
			i += 4
		}
		if (p.Int64()&3) == 3 {
			m = -kronecker(p.Int64(), n)
		} else {
			m = kronecker(p.Int64(), n)
		}
	}

	nn := big.NewInt(n)
	z := new(big.Int).Exp(nn, q, p)

	y.Set(z)
	t := new(big.Int).Sub(q, big.NewInt(1))
	t.Rsh(t, 1)

	x := new(big.Int).Exp(a, t, p)
	t.Mul(x, x).Mod(t, p)
	b := new(big.Int).Mul(t, a)
	b.Mod(b, p)
	x.Mul(a, x).Mod(x, p)

	for {
		if b.Cmp(big.NewInt(1)) == 0 {
			s.Set(x)
			return s
		}

		t.Mul(b, b).Mod(t, p)
		m := int64(1)
		for t.Cmp(big.NewInt(1)) != 0 {
			if m == r {
				return big.NewInt(0)
			}
			t.Mul(t, t).Mod(t, p)
			m++
		}

		t.Set(y)
		if r <= m {
			return big.NewInt(0)
		}
		for i := r - m - 1; i > 0; i-- {
			t.Mul(t, t).Mod(t, p)
		}
		y.Mul(t, t).Mod(y, p)
		r = m
		x.Mul(x, t).Mod(x, p)
		b.Mul(b, y).Mod(b, p)
	}
}

func squareRootMod3(a, p *big.Int) *big.Int {
	if modpos(p, big.NewInt(4)).Cmp(big.NewInt(3)) == 0 {
		pAdd1Div4 := new(big.Int).Div(new(big.Int).Add(p, big.NewInt(1)), big.NewInt(4))
		return expMod(a, pAdd1Div4, p)
	} else if modpos(p, big.NewInt(8)).Cmp(big.NewInt(5)) == 0 {
		pSub1Div4 := new(big.Int).Div(new(big.Int).Sub(p, big.NewInt(1)), big.NewInt(4))
		if modpos(expMod(a, pSub1Div4, p), p).Cmp(big.NewInt(1)) == 0 {
			pAdd3Div8 := new(big.Int).Div(new(big.Int).Add(p, big.NewInt(3)), big.NewInt(8))
			return expMod(a, pAdd3Div8, p)
		} else {
			pSub5Div8 := new(big.Int).Div(new(big.Int).Sub(p, big.NewInt(5)), big.NewInt(8))
			inner := expMod(new(big.Int).Mul(big.NewInt(4), a), pSub5Div8, p)
			return modpos(new(big.Int).Mul(new(big.Int).Mul(big.NewInt(2), a), inner), p)
		}
	}
	return big.NewInt(0)
}

func squareRootMod(a, p *big.Int) *big.Int {
	res3 := squareRootMod3(a, p)
	if res3.Sign() > 0 {
		return res3
	}

	res1 := squareRootMod1(a, p)
	if res1.Sign() > 0 {
		return res1
	}

	return mpzSqrtmod(a, p)
}

func printMpf(x *big.Float) {
	prec := x.Prec()
	digits := int(LOG2 * float64(prec))
	fmt.Printf("%.*f", digits, x)
}

func fSqrt(x *big.Float) *big.Float {
	return new(big.Float).SetPrec(precision).Sqrt(x)
}

func fFloor(x *big.Float) *big.Float {
	f, _ := x.Float64()
	return newFloat(math.Floor(f))
}

func fTrunc(x *big.Float) *big.Int {
	res := new(big.Int)
	x.Int(res)
	return res
}

func fAbs(x *big.Float) *big.Float {
	return new(big.Float).SetPrec(precision).Abs(x)
}

func sinf2(x *big.Float) *big.Float {
	if x.Sign() < 0 {
		negX := new(big.Float).Neg(x)
		return new(big.Float).Neg(sinf2(negX))
	}

	twoPI := new(big.Float).Mul(TWO, PIf)
	if x.Cmp(twoPI) > 0 {
		div := new(big.Float).Quo(x, twoPI)
		fl := fFloor(div)
		mod := new(big.Float).Sub(x, new(big.Float).Mul(twoPI, fl))
		return sinf2(mod)
	}

	if x.Cmp(PIf) > 0 {
		sub := new(big.Float).Sub(twoPI, x)
		return new(big.Float).Neg(sinf2(sub))
	}

	piDiv2 := new(big.Float).Quo(PIf, TWO)
	if x.Cmp(piDiv2) > 0 {
		sub := new(big.Float).Sub(PIf, x)
		return sinf2(sub)
	}

	i := big.NewInt(1)
	fact2n1 := new(big.Float).SetPrec(precision).SetFloat64(1)
	x2n1 := new(big.Float).Set(x)
	sinX := newFloat(0)
	oldSinX := newFloat(1)
	sign := true

	x2 := new(big.Float).Mul(x, x)

	for oldSinX.Cmp(sinX) != 0 {
		oldSinX.Set(sinX)

		term := new(big.Float).Quo(x2n1, fact2n1)
		if sign {
			sinX.Add(sinX, term)
		} else {
			sinX.Sub(sinX, term)
		}
		x2n1.Mul(x2n1, x2)

		i1 := new(big.Float).SetInt(new(big.Int).Add(i, big.NewInt(1)))
		i2 := new(big.Float).SetInt(new(big.Int).Add(i, big.NewInt(2)))
		fact2n1.Mul(fact2n1, new(big.Float).Mul(i1, i2))

		sign = !sign
		i.Add(i, big.NewInt(2))
	}

	return sinX
}

func cosf2(x *big.Float) *big.Float {
	if x.Sign() < 0 {
		return cosf2(new(big.Float).Neg(x))
	}

	twoPI := new(big.Float).Mul(TWO, PIf)
	if x.Cmp(twoPI) > 0 {
		div := new(big.Float).Quo(x, twoPI)
		fl := fFloor(div)
		mod := new(big.Float).Sub(x, new(big.Float).Mul(twoPI, fl))
		return cosf2(mod)
	}

	if x.Cmp(PIf) > 0 {
		sub := new(big.Float).Sub(twoPI, x)
		return cosf2(sub)
	}

	piDiv2 := new(big.Float).Quo(PIf, TWO)
	if x.Cmp(piDiv2) > 0 {
		sub := new(big.Float).Sub(PIf, x)
		return new(big.Float).Neg(cosf2(sub))
	}

	i := big.NewInt(0)
	fact2n := newFloat(1)
	x2n := newFloat(1)
	cosX := newFloat(0)
	oldCosX := newFloat(1)
	sign := true

	x2 := new(big.Float).Mul(x, x)

	for oldCosX.Cmp(cosX) != 0 {
		oldCosX.Set(cosX)

		term := new(big.Float).Quo(x2n, fact2n)
		if sign {
			cosX.Add(cosX, term)
		} else {
			cosX.Sub(cosX, term)
		}
		x2n.Mul(x2n, x2)

		i1 := new(big.Float).SetInt(new(big.Int).Add(i, big.NewInt(1)))
		i2 := new(big.Float).SetInt(new(big.Int).Add(i, big.NewInt(2)))
		fact2n.Mul(fact2n, new(big.Float).Mul(i1, i2))

		sign = !sign
		i.Add(i, big.NewInt(2))
	}

	return cosX
}

func atanf2(x *big.Float) *big.Float {
	if x.Cmp(ONE) == 0 {
		return new(big.Float).Quo(PIf, FOUR)
	}

	negOne := new(big.Float).Neg(ONE)
	if x.Cmp(negOne) == 0 {
		return new(big.Float).Quo(new(big.Float).Neg(PIf), FOUR)
	}

	if x.Cmp(ONE) > 0 {
		invX := new(big.Float).Quo(ONE, x)
		return new(big.Float).Sub(new(big.Float).Quo(PIf, TWO), atanf2(invX))
	}

	if x.Cmp(negOne) < 0 {
		invX := new(big.Float).Quo(ONE, x)
		return new(big.Float).Sub(new(big.Float).Quo(new(big.Float).Neg(PIf), TWO), atanf2(invX))
	}

	i := int64(1)
	twon1 := newFloat(1)
	x2n1 := new(big.Float).Set(x)
	atanX := newFloat(0)
	oldAtanX := newFloat(1)
	sign := true

	x2 := new(big.Float).Mul(x, x)

	for oldAtanX.Cmp(atanX) != 0 {
		if i > 1000000 {
			break
		}

		oldAtanX.Set(atanX)

		term := new(big.Float).Quo(x2n1, twon1)
		if sign {
			atanX.Add(atanX, term)
		} else {
			atanX.Sub(atanX, term)
		}

		x2n1.Mul(x2n1, x2)
		twon1.Add(twon1, TWO)
		sign = !sign
		i += 2
	}

	return atanX
}

func atan2f2(x, y *big.Float) *big.Float {
	r := newFloat(0)

	if x.Sign() == 0 && y.Sign() == 0 {
		return newFloat(0)
	}

	if fAbs(y).Cmp(fAbs(x)) >= 0 {
		r = atanf2(new(big.Float).Quo(x, y))
		if y.Sign() < 0 {
			if x.Sign() >= 0 {
				r.Add(r, PIf)
				return r
			}
			r.Sub(r, PIf)
			return r
		}
	} else {
		r = new(big.Float).Neg(atanf2(new(big.Float).Quo(y, x)))
		piDiv2 := new(big.Float).Quo(PIf, TWO)
		if x.Sign() < 0 {
			r.Sub(r, piDiv2)
			return r
		}
		r.Add(r, piDiv2)
		return r
	}

	return r
}

func logf2(x *big.Float) *big.Float {
	if x.Sign() <= 0 || x.Cmp(ONE) == 0 {
		return newFloat(0)
	}

	if x.Cmp(ONEPOINTNINE) > 0 {
		div := new(big.Float).Quo(x, ONEPOINTNINE)
		return new(big.Float).Add(logf2(div), NATLOGONEPOINTNINEf)
	}

	if x.Cmp(ONE) < 0 {
		mul := new(big.Float).Mul(x, Ef)
		return new(big.Float).Sub(logf2(mul), ONE)
	}

	xSub := new(big.Float).Sub(x, ONE)
	xN := new(big.Float).Set(xSub)
	logX := newFloat(0)
	oldLogX := newFloat(1)
	n := newFloat(1)
	sign := true

	for oldLogX.Cmp(logX) != 0 {
		oldLogX.Set(logX)

		term := new(big.Float).Quo(xN, n)
		if sign {
			logX.Add(logX, term)
		} else {
			logX.Sub(logX, term)
		}

		xN.Mul(xN, xSub)
		n.Add(n, ONE)
		sign = !sign
	}

	return logX
}

func expf2(x *big.Float) *big.Float {
	if x.Cmp(ONE) > 0 {
		sub := new(big.Float).Sub(x, ONE)
		return new(big.Float).Mul(expf2(sub), Ef)
	}

	if x.Sign() < 0 {
		add := new(big.Float).Add(x, ONE)
		return new(big.Float).Quo(expf2(add), Ef)
	}

	xN := new(big.Float).Set(x)
	expX := newFloat(0)
	oldExpX := newFloat(1)
	n := newFloat(1)

	for i := int64(1); oldExpX.Cmp(expX) != 0; i++ {
		oldExpX.Set(expX)

		term := new(big.Float).Quo(xN, n)
		expX.Add(expX, term)
		xN.Mul(xN, x)

		i1 := new(big.Float).SetFloat64(float64(i + 1))
		n.Mul(n, i1)
	}

	return new(big.Float).Add(ONE, expX)
}

func sinhf2(x *big.Float) *big.Float {
	negX := new(big.Float).Neg(x)
	diff := new(big.Float).Sub(expf2(x), expf2(negX))
	return new(big.Float).Quo(diff, TWO)
}

func coshf2(x *big.Float) *big.Float {
	negX := new(big.Float).Neg(x)
	sum := new(big.Float).Add(expf2(x), expf2(negX))
	return new(big.Float).Quo(sum, TWO)
}

func cabs2(u Complex) *big.Float {
	x2 := new(big.Float).Mul(u.x, u.x)
	y2 := new(big.Float).Mul(u.y, u.y)
	return fSqrt(new(big.Float).Add(x2, y2))
}

func cadd(u, v Complex) Complex {
	return Complex{
		x: new(big.Float).Add(u.x, v.x),
		y: new(big.Float).Add(u.y, v.y),
	}
}

func csub(u, v Complex) Complex {
	return Complex{
		x: new(big.Float).Sub(u.x, v.x),
		y: new(big.Float).Sub(u.y, v.y),
	}
}

func cdiv(u, v Complex) Complex {
	var temp1, temp2 *big.Float
	var w Complex

	if fAbs(v.x).Cmp(fAbs(v.y)) <= 0 {
		temp1 = new(big.Float).Quo(v.x, v.y)
		temp2 = new(big.Float).Add(v.y, new(big.Float).Mul(temp1, v.x))

		numX := new(big.Float).Add(new(big.Float).Mul(temp1, u.x), u.y)
		w.x = new(big.Float).Quo(numX, temp2)

		numY := new(big.Float).Sub(new(big.Float).Mul(temp1, u.y), u.x)
		w.y = new(big.Float).Quo(numY, temp2)
	} else {
		temp1 = new(big.Float).Quo(v.y, v.x)
		temp2 = new(big.Float).Add(v.x, new(big.Float).Mul(temp1, v.y))

		numX := new(big.Float).Add(u.x, new(big.Float).Mul(temp1, u.y))
		w.x = new(big.Float).Quo(numX, temp2)

		numY := new(big.Float).Sub(u.y, new(big.Float).Mul(temp1, u.x))
		w.y = new(big.Float).Quo(numY, temp2)
	}
	return w
}

func cmul(u, v Complex) Complex {
	uxvx := new(big.Float).Mul(u.x, v.x)
	uyvy := new(big.Float).Mul(u.y, v.y)
	uxvy := new(big.Float).Mul(u.x, v.y)
	uyvx := new(big.Float).Mul(u.y, v.x)

	return Complex{
		x: new(big.Float).Sub(uxvx, uyvy),
		y: new(big.Float).Add(uxvy, uyvx),
	}
}

func csqrt2(u Complex) Complex {
	r := fSqrt(cabs2(u))
	theta := atan2f2(u.y, u.x)
	phi := new(big.Float).Quo(theta, TWO)

	return Complex{
		x: new(big.Float).Mul(r, cosf2(phi)),
		y: new(big.Float).Mul(r, sinf2(phi)),
	}
}

func cexp2(u Complex) Complex {
	e := expf2(u.x)
	return Complex{
		x: new(big.Float).Mul(e, cosf2(u.y)),
		y: new(big.Float).Mul(e, sinf2(u.y)),
	}
}

func clog2(u Complex) Complex {
	r := cabs2(u)
	return Complex{
		x: logf2(r),
		y: atan2f2(u.y, u.x),
	}
}

func cpow2(u, v Complex) Complex {
	return cexp2(cmul(v, clog2(u)))
}

func round2(x *big.Float) *big.Int {
	if x.Sign() >= 0 {
		return fTrunc(new(big.Float).Add(x, HALF))
	}
	return fTrunc(new(big.Float).Sub(x, HALF))
}

func cpolyMul(m, n int64, a, b, c []Complex, p *int64) {
	*p = m + n
	for k := int64(0); k <= *p; k++ {
		sum := Complex{x: newFloat(0), y: newFloat(0)}
		for i := int64(0); i <= k; i++ {
			j := k - i
			var ai, bj Complex
			if i > m {
				ai = Complex{x: newFloat(0), y: newFloat(0)}
			} else {
				ai = a[i]
			}
			if j > n {
				bj = Complex{x: newFloat(0), y: newFloat(0)}
			} else {
				bj = b[j]
			}
			term := cmul(ai, bj)
			sum = cadd(sum, term)
		}
		c[k] = sum
	}
}

func Sum(q Complex) Complex {
	sign := newFloat(-1)
	errorTerm := newFloat(1)

	expon1 := Complex{x: newFloat(0), y: newFloat(0)}
	expon2 := Complex{x: newFloat(0), y: newFloat(0)}
	sum := Complex{x: newFloat(0), y: newFloat(0)}

	for i := int64(0); i < error_shift; i++ {
		errorTerm.Quo(errorTerm, TWO)
	}

	n := int64(1)
	for {
		e1 := float64(n * (3*n - 1) / 2)
		e2 := float64(n * (3*n + 1) / 2)

		expon1.x.SetFloat64(e1)
		expon2.x.SetFloat64(e2)

		term1 := cpow2(q, expon1)
		term2 := cpow2(q, expon2)
		term1 = cadd(term1, term2)

		term1.x.Mul(term1.x, sign)
		term1.y.Mul(term1.y, sign)

		sum = cadd(sum, term1)
		sign.Neg(sign)
		n++

		if cabs2(term1).Cmp(errorTerm) <= 0 {
			break
		}
	}

	sum.x.Add(sum.x, ONE)
	return sum
}

func Delta(q Complex) Complex {
	s := Complex{x: TWENTYFOUR, y: ZERO}
	return cmul(q, cpow2(Sum(q), s))
}

func Theta(D, A, B int64) Complex {
	fD := newFloat(float64(D))
	sqrtD := fSqrt(fD)
	fA := newFloat(float64(A))
	fB := newFloat(float64(B))

	s := Complex{
		x: new(big.Float).Quo(new(big.Float).Mul(new(big.Float).Neg(sqrtD), PIf), fA),
		y: new(big.Float).Quo(new(big.Float).Mul(new(big.Float).Neg(fB), PIf), fA),
	}

	return cexp2(s)
}

func jFunc(tau Complex) Complex {
	c := Complex{x: ZERO, y: new(big.Float).Mul(TWO, PIf)}
	twofiftysix := Complex{x: TWOHUNDREDFIFTYSIX, y: ZERO}
	oneC := Complex{x: ONE, y: ZERO}
	threeC := Complex{x: THREE, y: ZERO}

	q := cexp2(cmul(c, tau))
	q2 := cmul(q, q)
	f := cdiv(Delta(q2), Delta(q))

	f1 := cmul(twofiftysix, f)
	f1 = cadd(oneC, f1)
	f1 = cpow2(f1, threeC)

	return cdiv(f1, f)
}

func F(j, D, A, B int64) Complex {
	minustwentyfourth := Complex{x: new(big.Float).Quo(new(big.Float).Neg(ONE), TWENTYFOUR), y: newFloat(0)}
	twelth := Complex{x: new(big.Float).Quo(ONE, TWELVE), y: newFloat(0)}
	two := Complex{x: TWO, y: newFloat(0)}

	rootTwo := csqrt2(two)
	theta := Theta(D, A, B)

	theta24 := cpow2(theta, minustwentyfourth)
	theta12 := cpow2(theta, twelth)
	theta2 := cmul(theta, theta)

	minustheta := Complex{x: new(big.Float).Neg(theta.x), y: new(big.Float).Neg(theta.y)}

	var result1 Complex
	if j == 0 {
		result1 = Sum(minustheta)
	} else if j == 1 {
		result1 = Sum(theta)
	} else if j == 2 {
		result1 = Sum(cmul(cmul(theta, theta), cmul(theta, theta)))
	}

	result2 := cdiv(result1, Sum(theta2))

	var result Complex
	if j == 0 || j == 1 {
		result = cmul(theta24, result2)
	} else if j == 2 {
		result = cmul(rootTwo, cmul(theta12, result2))
	}

	return result
}

func G(D int64) int64 {
	if D%3 == 0 {
		return 3
	}
	return 1
}

func I(D int64) int64 {
	t1 := D % 8
	t2 := D % 3

	if t1 == 1 || t1 == 2 || t1 == 6 || t1 == 7 {
		return 3
	}
	if t1 == 3 && t2 != 0 {
		return 0
	}
	if t1 == 3 && t2 == 0 {
		return 2
	}
	if t1 == 5 {
		return 6
	}
	return 0
}

func J1(A, C int64) int64 {
	t1 := A * C
	t2 := t1 % 2

	if t2 == 1 {
		return 0
	}
	t2 = C % 2
	if t2 == 0 {
		return 1
	}
	t2 = A % 2
	if t2 == 0 {
		return 2
	}
	return 0
}

func K(D int64) int64 {
	t1 := D % 8
	if t1 == 1 || t1 == 2 || t1 == 6 {
		return 2
	}
	if t1 == 3 || t1 == 7 {
		return 1
	}
	if t1 == 5 {
		return 4
	}
	return 0
}

func L(D, A, C int64) int64 {
	t1 := D % 8
	t2 := (A * C) % 2
	t3 := C % 2
	var result int64

	if t2 == 1 || (t1 == 5 && t3 == 0) {
		result = A*A*C + A - C
	}
	if (t1 == 1 || t1 == 2 || t1 == 3 || t1 == 6 || t1 == 7) && t3 == 0 {
		result = A + C + C - A*C*C
	}

	t3 = A % 2
	if t1 == 3 && t3 == 0 {
		result = A - C + 5*A*C*C
	}
	if (t1 == 1 || t1 == 2 || t1 == 5 || t1 == 6 || t1 == 7) && t3 == 0 {
		result = A - C - A*C*C
	}

	return result
}

func M(A, C int64) int64 {
	t1 := A % 2

	if t1 == 1 {
		t2 := (A*A - 1) / 8
		t3 := t2 % 2
		if t3 == 0 {
			return 1
		}
		if t3 == 1 {
			return -1
		}
	}

	if t1 == 0 {
		t2 := (C*C - 1) / 8
		t3 := t2 % 2
		if t3 == 0 {
			return 1
		}
		if t3 == 1 {
			return -1
		}
	}

	return 0
}

func N(D, A, C int64) int64 {
	t1 := D % 8
	t2 := (A * C) % 2

	if t1 == 5 || (t1 == 3 && t2 == 1) || (t1 == 7 && t2 == 0) {
		return 1
	}
	if (t1 == 1 || t1 == 2 || t1 == 6) || (t1 == 7 && t2 == 1) {
		return M(A, C)
	}
	if t1 == 3 && t2 == 0 {
		return -M(A, C)
	}

	return 0
}

func uFunc(d, a, b, c int64) Complex {
	n := N(d, a, c)
	l := L(d, a, c)
	i := I(d)
	k := K(d)
	j := J1(a, c)
	g := G(d)

	f := F(j, d, a, b)

	temp1 := Complex{x: newFloat(float64(k)), y: newFloat(0)}
	temp2 := cpow2(f, temp1)

	t1 := (k * b * l) % 48
	if t1 < 0 {
		t1 += 48
	}

	temp3 := Complex{
		x: newFloat(0),
		y: new(big.Float).Mul(new(big.Float).Quo(new(big.Float).Neg(PIf), TWENTYFOUR), newFloat(float64(t1))),
	}

	temp1 = cexp2(temp3)
	fn := newFloat(float64(n))
	temp1.x.Mul(temp1.x, fn)
	temp1.y.Mul(temp1.y, fn)

	temp3 = Complex{x: newFloat(2), y: newFloat(0)}
	temp4 := Complex{x: new(big.Float).Quo(newFloat(float64(-i)), SIX), y: newFloat(0)}
	temp5 := cpow2(temp3, temp4)

	temp3 = cmul(temp1, temp5)
	temp4 = cmul(temp3, temp2)

	temp5 = Complex{x: newFloat(float64(g)), y: newFloat(0)}

	return cpow2(temp4, temp5)
}

func Hilbert(D int64, P []*big.Int, dP *int64) {
	PP := make([]Complex, POLY_SIZE)
	Q := make([]Complex, 3)
	R := make([]Complex, POLY_SIZE)

	for idx := 0; idx < POLY_SIZE; idx++ {
		PP[idx] = Complex{x: newFloat(0), y: newFloat(0)}
		R[idx] = Complex{x: newFloat(0), y: newFloat(0)}
	}

	DD := Complex{x: newFloat(float64(D)), y: newFloat(0)}
	sqrtD := csqrt2(DD)

	PP[0].x.SetFloat64(1)
	*dP = 0

	b := D % 2
	if b < 0 {
		b += 2
	}
	B := int64(math.Sqrt(math.Abs(float64(D)) / 3.0))

L2:
	t := (b*b - D) / 4
	a := b
	if a < 1 {
		a = 1
	}

L3:
	if t%a == 0 {
		aa := Complex{x: newFloat(float64(2 * a)), y: newFloat(0)}
		bb := Complex{x: newFloat(float64(-b)), y: newFloat(0)}

		tau := cdiv(cadd(bb, sqrtD), aa)
		J := jFunc(tau)

		if a == b || a*a == t || b == 0 {
			Q[0] = Complex{x: new(big.Float).Neg(J.x), y: new(big.Float).Neg(J.y)}
			Q[1] = Complex{x: newFloat(1), y: newFloat(0)}
			var dQ int64 = 1
			var dR int64
			cpolyMul(*dP, dQ, PP, Q, R, &dR)
			*dP = dR
			for i := int64(0); i <= dR; i++ {
				PP[i] = R[i]
			}
		} else {
			Q[0] = Complex{
				x: new(big.Float).Add(new(big.Float).Mul(J.x, J.x), new(big.Float).Mul(J.y, J.y)),
				y: newFloat(0),
			}
			Q[1] = Complex{x: new(big.Float).Mul(newFloat(-2), J.x), y: newFloat(0)}
			Q[2] = Complex{x: newFloat(1), y: newFloat(0)}
			var dQ int64 = 2
			var dR int64
			cpolyMul(*dP, dQ, PP, Q, R, &dR)
			*dP = dR
			for i := int64(0); i <= dR; i++ {
				PP[i] = R[i]
			}
		}
	}

	a++
	if a*a <= t {
		goto L3
	}

	b += 2
	if b <= B {
		goto L2
	}

	for i := int64(0); i <= *dP; i++ {
		P[i] = round2(PP[i].x)
	}
}

func Weber(D int64, P []*big.Int, dP *int64) {
	var dQ, dR int64
	PP := make([]Complex, POLY_SIZE)
	Q := make([]Complex, 3)
	R := make([]Complex, POLY_SIZE)

	for idx := 0; idx < POLY_SIZE; idx++ {
		PP[idx] = Complex{x: newFloat(0), y: newFloat(0)}
		R[idx] = Complex{x: newFloat(0), y: newFloat(0)}
	}

	if D%4 == 0 {
		D /= 4
	}

	help1 := int64(math.Sqrt(math.Abs(float64(D)) * 4.0 / 3.0))

	PP[0].x.SetFloat64(1)
	*dP = 0

	b := int64(0)
	for b <= help1 {
		t1 := b * b
		t2 := -D * 4
		t3 := t1 + t2
		t1 = 4

		t2 = t3 % t1
		if t2 == 0 {
			t1 = t3 / 4
			a := b
			if a < 1 {
				a = 1
			}

			x2 := int64(math.Sqrt(float64(t1)))
			for a <= x2 {
				h1 := t1 % a
				if h1 == 0 {
					C := t1 / a
					B1 := b
					A := a

					gcdVal := gcd(gcd(big.NewInt(A), big.NewInt(B1)), big.NewInt(C))
					if gcdVal.Cmp(big.NewInt(1)) == 0 {
						temp1 := B1 / 2
						J := uFunc(-D, A, temp1, C)

						if !(B1 > 0 && C > A && A > B1) {
							Q[0] = Complex{x: new(big.Float).Neg(J.x), y: new(big.Float).Neg(J.y)}
							Q[1] = Complex{x: newFloat(1), y: newFloat(0)}
							dQ = 1
						} else {
							Q[0] = Complex{
								x: new(big.Float).Add(new(big.Float).Mul(J.x, J.x), new(big.Float).Mul(J.y, J.y)),
								y: newFloat(0),
							}
							Q[1] = Complex{x: new(big.Float).Mul(newFloat(-2), J.x), y: newFloat(0)}
							Q[2] = Complex{x: newFloat(1), y: newFloat(0)}
							dQ = 2
						}

						cpolyMul(*dP, dQ, PP, Q, R, &dR)
						*dP = dR
						for i := int64(0); i <= dR; i++ {
							PP[i] = R[i]
						}
					}
				}
				a++
			}
		}
		b++
	}

	for i := int64(0); i <= *dP; i++ {
		P[i] = round2(PP[i].x)
	}
}

func Vegas(u, N *big.Int, d int64) *big.Int {
	var j *big.Int
	two := big.NewInt(2)
	three := big.NewInt(3)
	four := big.NewInt(4)
	eight := big.NewInt(8)
	A := big.NewInt(0)
	passthrough := false

	mod8 := d % 8
	if mod8 < 0 {
		mod8 += 8
	}

	switch mod8 {
	case 7: // -1 mod 8
		A = new(big.Int).Mul(big.NewInt(4), expMod(inverse(u, N), four, N))
	case 6, 2: // -2, -6 mod 8
		A = new(big.Int).Mul(big.NewInt(-4), expMod(u, four, N))
	case 5: // -3 mod 8
		A = new(big.Int).Mul(big.NewInt(16), expMod(inverse(u, N), eight, N))
	case 4: // -4 mod 8
		A = new(big.Int).Mul(big.NewInt(-8), expMod(u, two, N))
	case 3: // -5 mod 8
		A = new(big.Int).Mul(big.NewInt(4), expMod(inverse(u, N), two, N))
	case 1: // -7 mod 8
		A = expMod(inverse(u, N), eight, N)
	default:
		passthrough = true
	}

	if d%3 != 0 {
		A = expMod(A, three, N)
	}

	term1 := inverse(A, N)
	term2 := expMod(new(big.Int).Sub(A, big.NewInt(16)), three, N)
	j = modpos(new(big.Int).Mul(term1, term2), N)

	if passthrough {
		j = u
	}

	return j
}

func modifiedCornacchia(D, p *big.Int, x, y **big.Int) int {
	value := 0

	if JACOBI(D, p) != -1 {
		x0 := squareRootMod(D, p)

		dd := modpos(D, big.NewInt(2))
		xx := modpos(x0, big.NewInt(2))

		if dd.Cmp(xx) != 0 {
			x0 = new(big.Int).Sub(p, x0)
		}

		a := new(big.Int).Mul(p, big.NewInt(2))
		b := new(big.Int).Set(x0)
		c := new(big.Int).Sqrt(p)

		l := new(big.Int).Mul(c, big.NewInt(2))

		for b.Cmp(l) > 0 {
			r := modpos(a, b)
			a.Set(b)
			b.Set(r)
		}

		c = new(big.Int).Mul(p, big.NewInt(4))
		a = new(big.Int).Mul(b, b)
		e := new(big.Int).Sub(c, a)
		dVal := new(big.Int).Abs(D)

		c = new(big.Int).Div(e, dVal)
		r := modpos(e, dVal)

		isSq, rootY := squareTest(c)
		if r.Sign() == 0 && isSq {
			*x = b
			*y = rootY
			value = 1
		}
	}

	return value
}

func zpolyPrint(da int64, za []*big.Int) {
	if Quiet == 0 {
		for i := da; i >= 0; i-- {
			fmt.Printf("%s ", za[i].String())
		}
		fmt.Println()
	}
}

func myzmulmod(res, x, y, m *big.Int) {
	temp := new(big.Int).Mul(x, y)
	res.Mod(temp, m)
}

func myzdivmod(res, x, y, m *big.Int) {
	h1 := new(big.Int).ModInverse(y, m)
	if h1 == nil {
		fmt.Printf("inverse is undefined!\ncomposite\n")
		os.Exit(2)
	}
	myzmulmod(res, x, h1, m)
}

func zpolyCopy(da int64, za, zb []*big.Int, db *int64) {
	*db = da
	for i := int64(0); i <= da; i++ {
		zb[i].Set(za[i])
	}
}

func zpolyMul(m, n int64, za, zb, zc []*big.Int, p *int64) {
	*p = m + n

	zsum := new(big.Int)
	zterm := new(big.Int)
	zai := new(big.Int)
	zbk := new(big.Int)

	for k := int64(0); k <= *p; k++ {
		zsum.SetInt64(0)

		for i := int64(0); i <= k; i++ {
			j := k - i

			if i > m {
				zai.SetInt64(0)
			} else {
				zai.Set(za[i])
			}

			if j > n {
				zbk.SetInt64(0)
			} else {
				zbk.Set(zb[j])
			}

			zterm.Mul(zai, zbk)
			zsum.Add(zsum, zterm)
		}
		zc[k].Set(zsum)
	}
}

func zpolyDiv(m, n int64, zu, zv, zq, zr []*big.Int, p, s *int64) {
	zvn := new(big.Int).Set(zv[n])
	za := new(big.Int)
	zb := new(big.Int)

	for j := int64(0); j <= m; j++ {
		zr[j].Set(zu[j])
	}

	if m < n {
		*p = 0
		*s = m
		zq[0].SetInt64(0)
	} else {
		*p = m - n
		*s = n - 1

		for k := *p; k >= 0; k-- {
			nk := n + k
			za.Exp(zvn, big.NewInt(k), nil)
			zq[k].Mul(zr[nk], za)

			for j := nk - 1; j >= 0; j-- {
				jk := j - k
				if jk >= 0 {
					za.Mul(zvn, zr[j])
					zb.Mul(zr[nk], zv[jk])
					zr[j].Sub(za, zb)
				} else {
					za.Set(zr[j])
					zr[j].Mul(zvn, za)
				}
			}
		}

		for *p > 0 && zq[*p].Sign() == 0 {
			*p--
		}

		for *s > 0 && zr[*s].Sign() == 0 {
			*s--
		}
	}
}

func zpolyMod(zp *big.Int, za []*big.Int, da *int64) {
	zb := new(big.Int)

	for i := int64(0); i <= *da; i++ {
		zb.Mod(za[i], zp)
		za[i].Set(zb)
	}

	for *da > 0 && za[*da].Sign() == 0 {
		*da--
	}
}

func zpolyPow(degreeA, degreem int64, zn, zp *big.Int, zA, zm, zs []*big.Int, ds *int64) {
	var dP, dq int64
	dx := degreeA

	za := new(big.Int).Set(zn)
	zb := new(big.Int)

	zP := make([]*big.Int, POLY_SIZE)
	zq := make([]*big.Int, POLY_SIZE)
	zx := make([]*big.Int, POLY_SIZE)
	zy := make([]*big.Int, POLY_SIZE)

	for i := 0; i < POLY_SIZE; i++ {
		zP[i] = new(big.Int)
		zq[i] = new(big.Int)
		zx[i] = new(big.Int)
		zy[i] = new(big.Int)
	}

	*ds = 0
	zs[0].SetInt64(1)

	for i := int64(0); i <= dx; i++ {
		zx[i].Set(zA[i])
	}

	for za.Sign() > 0 {
		if za.Bit(0) == 1 {
			zpolyMul(*ds, dx, zs, zx, zP, &dP)
			zpolyDiv(dP, degreem, zP, zm, zq, zs, &dq, ds)
			zpolyMod(zp, zs, ds)
		}

		zb.Set(za)
		za.Rsh(zb, 1)

		if za.Sign() > 0 {
			for i := int64(0); i <= dx; i++ {
				zy[i].Set(zx[i])
			}

			zpolyMul(dx, dx, zx, zy, zP, &dP)
			zpolyDiv(dP, degreem, zP, zm, zq, zx, &dq, &dx)
			zpolyMod(zp, zx, &dx)
		}
	}
}

func zpolyGcd(degreeA, degreeB int64, zp *big.Int, zA, zB, za []*big.Int, da *int64) {
	nonzero := false
	var db, dq, dr int64

	zc := new(big.Int)
	zb := make([]*big.Int, POLY_SIZE)
	zq := make([]*big.Int, POLY_SIZE)
	zr := make([]*big.Int, POLY_SIZE)

	for i := 0; i < POLY_SIZE; i++ {
		zb[i] = new(big.Int)
		zq[i] = new(big.Int)
		zr[i] = new(big.Int)
	}

	if degreeA > degreeB {
		*da = degreeA
		db = degreeB

		for i := int64(0); i <= *da; i++ {
			za[i].Set(zA[i])
		}
		for i := int64(0); i <= db; i++ {
			zb[i].Set(zB[i])
		}
	} else {
		*da = degreeB
		db = degreeA

		for i := int64(0); i <= *da; i++ {
			za[i].Set(zB[i])
		}
		for i := int64(0); i <= db; i++ {
			zb[i].Set(zA[i])
		}
	}

	for i := int64(0); i <= db && !nonzero; i++ {
		nonzero = zb[i].Sign() != 0
	}

	for nonzero {
		zpolyDiv(*da, db, za, zb, zq, zr, &dq, &dr)

		for i := int64(0); i <= dr; i++ {
			zc.Set(zr[i])
			zr[i].Mod(zc, zp)
		}

		zero := true
		for i := dr; i >= 0 && zero; i-- {
			zero = zr[i].Sign() == 0
			if zero && dr > 0 {
				dr--
			}
		}

		for i := int64(0); i <= db; i++ {
			za[i].Set(zb[i])
		}
		*da = db

		for i := int64(0); i <= dr; i++ {
			zb[i].Set(zr[i])
		}
		db = dr

		nonzero = false
		for i := int64(0); i <= db && !nonzero; i++ {
			nonzero = zb[i].Sign() != 0
		}
	}
}

func Recurse(degreeA int64, zp *big.Int, zA, zroot []*big.Int, rootSize *int64) {
	var dd, degreeB, dq, dr int64
	du := int64(1)
	flag := 0

	za := new(big.Int)
	zb := new(big.Int)
	zn := new(big.Int)
	x0 := big.NewInt(102)

	zB := make([]*big.Int, POLY_SIZE)
	zd := make([]*big.Int, POLY_SIZE)
	zq := make([]*big.Int, POLY_SIZE)
	zr := make([]*big.Int, POLY_SIZE)

	for i := 0; i < POLY_SIZE; i++ {
		zB[i] = new(big.Int)
		zd[i] = new(big.Int)
		zq[i] = new(big.Int)
		zr[i] = new(big.Int)
	}

	zu := []*big.Int{new(big.Int), new(big.Int)}

	if zA[degreeA].Cmp(big.NewInt(1)) != 0 {
		for i := int64(0); i < (degreeA + 1); i++ {
			myzdivmod(zA[i], zA[i], zA[degreeA], zp)
		}
	}

	for degreeA != 1 {
		for {
			za.Sub(zp, big.NewInt(1))
			zn.Rsh(za, 1)

			x0.Add(x0, big.NewInt(1))

			zu[0].Set(x0)
			zu[1].SetInt64(1)

			zpolyMod(zp, zu, &du)

			zpolyPow(du, degreeA, zn, zp, zu, zA, zd, &dd)
			zpolyMod(zp, zd, &dd)

			zd[0].Sub(zd[0], big.NewInt(1))

			zpolyGcd(dd, degreeA, zp, zd, zA, zB, &degreeB)
			zpolyMod(zp, zB, &degreeB)

			if x0.Cmp(big.NewInt(200)) > 0 || *rootSize > (degreeA-1) {
				flag = 1
				goto L1
			}

			if degreeB != 0 && degreeB != degreeA {
				break
			}
		}

		if degreeB >= 1 && flag != 1 {
			Recurse(degreeB, zp, zB, zroot, rootSize)

			zpolyDiv(degreeA, degreeB, zA, zB, zq, zr, &dq, &dr)
			zpolyMod(zp, zq, &dq)
			zpolyCopy(dq, zq, zA, &degreeA)

			Recurse(degreeA, zp, zA, zroot, rootSize)
		}
	}

	if degreeA == 1 {
		za.ModInverse(zA[1], zp)
		zb.Mul(zA[0], za)
		zb.Neg(zb)
		zroot[*rootSize].Mod(zb, zp)
		*rootSize++
	}

L1:
}

func FindRootsModuloAPrime(degreeP int64, p *big.Int, P, root []*big.Int, rootSize *int64) {
	zp := new(big.Int).Set(p)

	zA := make([]*big.Int, POLY_SIZE)
	zroot := make([]*big.Int, POLY_SIZE)

	for i := 0; i < POLY_SIZE; i++ {
		zA[i] = new(big.Int).Set(P[i])
		zroot[i] = new(big.Int).Set(root[i])
	}

	*rootSize = 0
	Recurse(degreeP, zp, zA, zroot, rootSize)

	for i := 0; i < POLY_SIZE; i++ {
		P[i].Set(zA[i])
		root[i].Set(zroot[i])
	}

	for i := int64(0); i < *rootSize-1; i++ {
		for j := i + 1; j < *rootSize; j++ {
			if root[i].Cmp(root[j]) > 0 {
				root[i], root[j] = root[j], root[i]
			}
		}
	}
}

type ecmResult struct {
	g     *big.Int
	found bool
}

func LenstrasECM(N, g **big.Int, Bmax int64) int {
	B := int64(1000)
	
	// Determine the worker pool size dynamically from the global setting or runtime CPU availability
	numWorkers := threads
	if numWorkers <= 0 {
		numWorkers = runtime.GOMAXPROCS(0)
	}

	for B < Bmax {
		type job struct {
			a *big.Int
		}

		jobs := make(chan job, numWorkers)
		results := make(chan ecmResult, numWorkers)
		done := make(chan struct{})

		for w := 0; w < numWorkers; w++ {
			go func(workerID int) {
//				localRgen := rand.New(rand.NewSource(time.Now().UnixNano() + int64(workerID)))

				for {
					select {
					case <-done:
						return
					case j, ok := <-jobs:
						if !ok {
							return
						}

						var x, y Point
						var d *big.Int
						x.x = big.NewInt(0)
						x.y = big.NewInt(1)

						found := 0
						newq := int64(2)

						for newq < B && found != 1 {
							select {
							case <-done:
								return
							default:
							}

							q := newq
							q1 := q
							l := B / q
							for q1 <= l {
								q1 *= q
							}

							found = multiply(j.a, big.NewInt(q1), *N, x, &y, &d)
							x.x = y.x
							x.y = y.y

							newq = nextp(big.NewInt(q)).Int64()
						}

						factor := gcd(d, *N)
						if factor.Cmp(*N) != 0 && factor.Cmp(big.NewInt(1)) != 0 {
							select {
							case results <- ecmResult{g: factor, found: true}:
							case <-done:
							}
							return
						}

						select {
						case results <- ecmResult{g: factor, found: false}:
						case <-done:
						}
					}
				}
			}(w)
		}

		var foundFactor *big.Int
		var factorFound bool

		go func() {
			defer close(jobs)
			for i := 0; i < 20; i++ {
				// Use local randomness to prevent lock contention
				a := modpos(big.NewInt(int64(rand.Uint32())), *N)
				select {
				case jobs <- job{a: a}:
				case <-done:
					return
				}
			}
		}()

		for i := 0; i < 20; i++ {
			res := <-results
			if res.found {
				foundFactor = res.g
				factorFound = true
				close(done)
				break
			}
		}

		if !factorFound {
			close(done)
		}

		if factorFound {
			*g = foundFactor
			*N = new(big.Int).Div(*N, *g)
			return 1
		}

		B *= 5
	}

	*g = big.NewInt(1)
	return 0
}

func checkForFactor(q **big.Int, m, t *big.Int) bool {
	*q = new(big.Int).Set(m)

	if RabinMiller(*q) {
		return false
	}

	two := big.NewInt(2)
	three := big.NewInt(3)
	rem := new(big.Int)

	for {
		div, r := new(big.Int).DivMod(*q, two, rem)
		if r.Sign() == 0 {
			*q = div
		} else {
			break
		}
	}

	for {
		div, r := new(big.Int).DivMod(*q, three, rem)
		if r.Sign() == 0 {
			*q = div
		} else {
			break
		}
	}

	if (*q).Cmp(t) < 0 {
		return false
	}
	if (*q).Cmp(m) < 0 && RabinMiller(*q) {
		return true
	}

	d := big.NewInt(1)
	oldq := new(big.Int)

	for {
		oldq.Set(*q)
		LenstrasECM(q, &d, Bmax)

		if (*q).Cmp(t) < 0 {
			return false
		}
		if (*q).Cmp(m) < 0 && RabinMiller(*q) {
			return true
		}

		if (*q).Cmp(oldq) >= 0 {
			break
		}
	}

	return false
}

func findCurve(typeVal int, a, b **big.Int, D int64, N *big.Int, root []*big.Int, rootSize *int64) bool {
	T := make([]*big.Int, POLY_SIZE)
	for i := 0; i < POLY_SIZE; i++ {
		T[i] = new(big.Int)
	}
	var dT int64

	*rootSize = 0

	if typeVal == 0 {
		if D == -3 {
			*a = big.NewInt(0)
			*b = big.NewInt(-1)
			*rootSize = 1
			return true
		} else if D == -4 {
			*a = big.NewInt(-1)
			*b = big.NewInt(0)
			*rootSize = 1
			return true
		}
	}

	if hilbert != 0 && typeVal == 1 {
		Hilbert(D, T, &dT)

		if Quiet == 0 {
			fmt.Printf("D = %d, dT = %d, T = ", D, dT)
			zpolyPrint(dT, T)
		}

		smallestCoeff := T[0]
		isCube, _ := cubeTest(smallestCoeff)
		if !isCube {
			if Quiet == 0 {
				fmt.Println("HCP loss of precision")
			}
			*rootSize = 0
			return false
		}
	}

	if weber != 0 && typeVal == 2 && D%32 != 0 {
		Weber(D, T, &dT)

		if Quiet == 0 {
			fmt.Printf("D = %d, dW = %d, W = ", D, dT)
			zpolyPrint(dT, T)
		}

		smallestCoeff := T[0]
		if !poweroftwoTest(smallestCoeff) {
			if Quiet == 0 {
				fmt.Println("WCP loss of precision")
			}
			*rootSize = 0
			return false
		}
	}

	if (hilbert != 0 && typeVal == 1) || (weber != 0 && typeVal == 2 && D%32 != 0) {
		zp := new(big.Int).Set(N)
		zA := make([]*big.Int, POLY_SIZE)
		for i := 0; i < POLY_SIZE; i++ {
			zA[i] = new(big.Int).Set(T[i])
		}

		zpolyMod(zp, zA, &dT)
		for i := 0; i < POLY_SIZE; i++ {
			T[i].Set(zA[i])
		}

		FindRootsModuloAPrime(dT, N, T, root, rootSize)
	}

	return *rootSize > 0
}

func Atkin(N *big.Int) int {
	var value1, value2 int
	var Ni = new(big.Int).Set(N)
	var a, b, d, m, q, t, x, y *big.Int
	var P, P1, P2 Point
	var k int64
	var D int64
	found := false
	found2 := false
	var u, v *big.Int
	var g *big.Int
	var pointsTried int64

	root := make([]*big.Int, POLY_SIZE)
	for i := 0; i < POLY_SIZE; i++ {
		root[i] = new(big.Int)
	}
	var rootSize int64
	var j, w *big.Int

	iStep := int64(0)

	for {
		if Ni.Cmp(big.NewInt(SIEVE_LIMIT)) <= 0 {
			p := int64(2)
			niFloat, _ := new(big.Float).SetInt(Ni).Float64()
			sqrtNi := int64(math.Sqrt(niFloat))

			for p <= sqrtNi {
				if new(big.Int).Mod(Ni, big.NewInt(p)).Sign() == 0 {
					fmt.Printf("1 factor = %d\n", p)
					return 2
				}
				p++
			}
			return 0
		}

		if !RabinMiller(Ni) {
			return 2
		}

		for Bmax <= 2000000000 && Dmax <= 312500 {
			if Quiet == 0 {
				fmt.Printf("Bmax = %d\n", Bmax)
				fmt.Printf("Dmax = %d\n", Dmax)
			}

			n := int64(1)

			for {
				D = -n
				n++
				if D <= -Dmax {
					break
				}

				if D%4 != 0 && D%4 != -3 && D%4 != 1 {
					continue
				}

				found = false
				found2 = false

				if verbose != 0 {
					fmt.Printf("%d\r", D)
				}

				if JACOBI(new(big.Int).Add(big.NewInt(D), Ni), Ni) != 1 {
					continue
				}

				if modifiedCornacchia(big.NewInt(D), Ni, &u, &v) == 0 {
					continue
				}

				niFloat, _ := new(big.Float).SetInt(Ni).Float64()
				tVal := int64(math.Sqrt(math.Sqrt(niFloat))) + 1
				t = big.NewInt(tVal * tVal)

				m = new(big.Int).Add(Ni, big.NewInt(1))
				m.Add(m, u)

				if checkForFactor(&q, m, t) {
					found = true
				} else {
					m = new(big.Int).Add(Ni, big.NewInt(1))
					m.Sub(m, u)

					if checkForFactor(&q, m, t) {
						found = true
					} else if D == -4 {
						twoV := new(big.Int).Mul(big.NewInt(2), v)
						m = new(big.Int).Add(Ni, big.NewInt(1))
						m.Add(m, twoV)

						if checkForFactor(&q, m, t) {
							found = true
						} else {
							m = new(big.Int).Add(Ni, big.NewInt(1))
							m.Sub(m, twoV)

							if checkForFactor(&q, m, t) {
								found = true
							}
						}
					} else if D == -3 {
						threeV := new(big.Int).Mul(big.NewInt(3), v)
						uAdd3vDiv2 := new(big.Int).Div(new(big.Int).Add(u, threeV), big.NewInt(2))
						uSub3vDiv2 := new(big.Int).Div(new(big.Int).Sub(u, threeV), big.NewInt(2))

						m1 := new(big.Int).Add(new(big.Int).Add(Ni, big.NewInt(1)), uAdd3vDiv2)
						m2 := new(big.Int).Sub(new(big.Int).Add(Ni, big.NewInt(1)), uAdd3vDiv2)
						m3 := new(big.Int).Add(new(big.Int).Add(Ni, big.NewInt(1)), uSub3vDiv2)
						m4 := new(big.Int).Sub(new(big.Int).Add(Ni, big.NewInt(1)), uSub3vDiv2)

						if checkForFactor(&q, m1, t) || checkForFactor(&q, m2, t) ||
							checkForFactor(&q, m3, t) || checkForFactor(&q, m4, t) {
							found = true
						}
					}
				}

				if !found {
					continue
				}

				rootSize = 0

				for typeVal := 0; typeVal <= 2; typeVal++ {
					if !findCurve(typeVal, &a, &b, D, Ni, root, &rootSize) {
						continue
					}

					for rootsTried := int64(0); rootsTried < rootSize; rootsTried++ {
						if typeVal == 0 {
							a = modpos(a, Ni)
							b = modpos(b, Ni)
						} else if hilbert != 0 && typeVal == 1 {
							j = modpos(root[rootsTried], Ni)

							if Quiet == 0 {
								fmt.Printf("j = %s\n", j.String())
							}

							jSub1728 := new(big.Int).Sub(j, big.NewInt(1728))
							c := modpos(new(big.Int).Mul(j, inverse(jSub1728, Ni)), Ni)
							a = modpos(new(big.Int).Mul(big.NewInt(-3), c), Ni)
							b = modpos(new(big.Int).Mul(big.NewInt(2), c), Ni)
						} else if weber != 0 && typeVal == 2 {
							w = modpos(root[rootsTried], Ni)

							if Quiet == 0 {
								fmt.Printf("u = %s\n", w.String())
							}

							if D%4 == 0 {
								j = Vegas(w, Ni, D/4)
							} else {
								j = Vegas(w, Ni, D)
							}

							if Quiet == 0 {
								fmt.Printf("j = %s\n", j.String())
							}

							jSub1728 := new(big.Int).Sub(j, big.NewInt(1728))
							c := modpos(new(big.Int).Mul(j, inverse(jSub1728, Ni)), Ni)
							a = modpos(new(big.Int).Mul(big.NewInt(-3), c), Ni)
							b = modpos(new(big.Int).Mul(big.NewInt(2), c), Ni)
						}

						for {
							for {
								g = modpos(rand2(), Ni)
								if g.Sign() != 0 {
									break
								}
							}
							if JACOBI(g, Ni) != -1 {
								continue
							}
							if D == -3 {
								expVal := expMod(g, new(big.Int).Div(new(big.Int).Sub(Ni, big.NewInt(1)), big.NewInt(3)), Ni)
								if expVal.Cmp(big.NewInt(1)) == 0 {
									continue
								}
							}
							break
						}

						pointsTried = 0

						for {
							for {
								for {
									for {
										x = modpos(rand2(), Ni)
										if x.Sign() != 0 {
											break
										}
									}
									x2 := modpos(new(big.Int).Mul(x, x), Ni)
									x3 := modpos(new(big.Int).Mul(x2, x), Ni)
									ax := new(big.Int).Mul(a, x)
									y = modpos(new(big.Int).Add(new(big.Int).Add(x3, ax), b), Ni)

									if JACOBI(y, Ni) != -1 {
										break
									}
								}
								y = squareRootMod(y, Ni)
								if y.Sign() != 0 {
									break
								}
							}

							P.x = x
							P.y = y
							pointsTried++
							k = 0

							for {
								mDivQ := new(big.Int).Div(m, q)
								value2 = multiply(a, mDivQ, Ni, P, &P2, &d)

								if value2 == 1 {
									fmt.Printf("3 factor = %s\n", d.String())
									return 2
								}

								value1 = multiply(a, q, Ni, P2, &P1, &d)

								if value1 == 1 {
									fmt.Printf("2 factor = %s\n", d.String())
									return 2
								}

								if value1 == -1 && value2 == 0 {
									found2 = true
									break
								}

								k++

								if D == -3 {
									if k >= 6 {
										break
									}
									b = new(big.Int).Mul(b, g)
								} else if D == -4 {
									if k >= 4 {
										break
									}
									a = new(big.Int).Mul(a, g)
								} else {
									if k >= 2 {
										break
									}
									g2 := new(big.Int).Mul(g, g)
									g3 := new(big.Int).Mul(g2, g)
									a = new(big.Int).Mul(a, g2)
									b = new(big.Int).Mul(b, g3)
								}

								a = modpos(a, Ni)
								b = modpos(b, Ni)
							}

							if found2 || pointsTried >= 100 {
								break
							}
						}

						if found2 {
							break
						}
					}

					if found2 {
						break
					}
				}

				if found2 {
					break
				}
			}

			if found2 {
				if !staticBmax {
					Bmax = BMAX
				}
				if !staticDmax {
					Dmax = DMAX
				}
				break
			} else {
				if !staticBmax {
					Bmax *= 10
				}
				if !staticDmax {
					Dmax *= 5
				}
			}
		}

		if Dmax > 312500 {
			if Quiet == 0 {
				fmt.Println("ProvePrime: ran out of discriminants")
			}
			return 2
		}
		if Bmax > 2000000000 {
			if Quiet == 0 {
				fmt.Println("ProvePrime: exceeded maximum factoring bounds")
			}
			return 2
		}

		fmt.Printf("N[%d] = %s\n", iStep, Ni.String())
		fmt.Printf("a = %s\n", a.String())
		fmt.Printf("b = %s\n", b.String())
		fmt.Printf("m = %s\n", m.String())
		fmt.Printf("q = %s\n", q.String())
		fmt.Printf("P = (%s, %s)\n", P.x.String(), P.y.String())
		fmt.Printf("P1 = (%s, %s)\n", P1.x.String(), P1.y.String())
		fmt.Printf("P2 = (%s, %s)\n", P2.x.String(), P2.y.String())

		iStep++
		Ni.Set(q)

		if one != 0 {
			break
		}
	}

	if one == 0 {
		return 0
	}
	return 1
}

func initGlobals() {
	if precision == 0 {
		precision = PRECISION
	}

	PIf = newFloat(3)
	Ef = newFloat(2)
	NATLOGONEPOINTNINEf = newFloat(1)

	ZERO = newFloat(0)
	ONE = newFloat(1)
	TWO = newFloat(2)
	THREE = newFloat(3)
	FOUR = newFloat(4)
	FIVE = newFloat(5)
	SIX = newFloat(6)
	EIGHT = newFloat(8)
	TEN = newFloat(10)
	TWELVE = newFloat(12)
	EIGHTEEN = newFloat(18)
	NINETEEN = newFloat(19)
	TWENTYFOUR = newFloat(24)
	FIFTYSEVEN = newFloat(57)
	TWOHUNDREDTHIRTYNINE = newFloat(239)
	TWOHUNDREDFIFTYSIX = newFloat(256)

	HALF = new(big.Float).Quo(ONE, TWO)
	ONEPOINTNINE = new(big.Float).Quo(NINETEEN, TEN)

	term1 := atanf2(new(big.Float).Quo(ONE, TWO))
	term2 := atanf2(new(big.Float).Quo(ONE, THREE))
	PIf = new(big.Float).Mul(FOUR, new(big.Float).Add(term1, term2))

	Ef = expf2(ONE)
	NATLOGONEPOINTNINEf = logf2(ONEPOINTNINE)
}

func main() {
	flag.IntVar(&Quiet, "Quiet", 0, "Print very reduced messages.")
	flag.IntVar(&Quiet, "Q", 0, "Print very reduced messages.")
	flag.IntVar(&quiet, "quiet", 0, "Print reduced messages.")
	flag.IntVar(&quiet, "q", 0, "Print reduced messages.")
	flag.IntVar(&verbose, "verbose", 0, "Print verbose messages.")
	flag.IntVar(&verbose, "v", 0, "Print verbose messages.")
	flag.IntVar(&one, "one", 0, "Run just one iteration before termination.")
	flag.IntVar(&one, "o", 0, "Run just one iteration before termination.")
	flag.IntVar(&hilbert, "Hilbert", 0, "Use Hilbert polynomials (only).")
	flag.IntVar(&hilbert, "H", 0, "Use Hilbert polynomials (only).")
	flag.IntVar(&weber, "Weber", 0, "Use Weber polynomials (only).")
	flag.IntVar(&weber, "W", 0, "Use Weber polynomials (only).")
	flag.IntVar(&threads, "threads", 0, "Set worker threads/goroutines limit for ECM.")
	flag.IntVar(&threads, "t", 0, "Set worker threads/goroutines limit for ECM.")

	var seedVal int64
	var precVal int64
	var errorShiftVal int64
	var bmaxVal int64
	var dmaxVal int64

	flag.Int64Var(&seedVal, "seed", 0, "Set (pseudo-)random seed.")
	flag.Int64Var(&seedVal, "s", 0, "Set (pseudo-)random seed.")
	flag.Int64Var(&precVal, "precision", 0, "Set FP precision.")
	flag.Int64Var(&precVal, "p", 0, "Set FP precision.")
	flag.Int64Var(&errorShiftVal, "error_shift", 0, "Set precision in CP generation.")
	flag.Int64Var(&errorShiftVal, "e", 0, "Set precision in CP generation.")
	flag.Int64Var(&bmaxVal, "Bmax", 0, "Set max ECM factoring bound.")
	flag.Int64Var(&bmaxVal, "B", 0, "Set max ECM factoring bound.")
	flag.Int64Var(&dmaxVal, "Dmax", 0, "Set max discriminant bound.")
	flag.Int64Var(&dmaxVal, "D", 0, "Set max discriminant bound.")

	flag.Parse()

	// If the threads CLI flag is specified, configure GOMAXPROCS accordingly
	if threads > 0 {
		runtime.GOMAXPROCS(threads)
	} else {
		threads = runtime.NumCPU()
	}

	if seedVal != 0 {
		seed = seedVal
	} else {
		seed = time.Now().UnixNano()
	}

	rgen = rand.New(rand.NewSource(seed))

	if bmaxVal != 0 {
		Bmax = bmaxVal
		staticBmax = true
	} else {
		Bmax = BMAX
	}

	if dmaxVal != 0 {
		Dmax = dmaxVal
		staticDmax = true
	} else {
		Dmax = DMAX
	}

	if errorShiftVal != 0 {
		error_shift = errorShiftVal
	} else {
		error_shift = ERROR_SHIFT
	}

	if precVal != 0 {
		precision = uint(precVal)
	} else {
		precision = PRECISION
	}

	if hilbert == 0 && weber == 0 {
		hilbert = 1
		weber = 1
	}

	initGlobals()

	if Quiet == 0 {
		fmt.Printf("random seed = %d\n", seed)
		fmt.Printf("threads = %d\n", threads)
		fmt.Printf("error_shift = %d\n", error_shift)
		fmt.Printf("precision = %d\n", precision)
	}

	if Quiet == 0 && quiet == 0 {
		fmt.Print("PI = ")
		printMpf(PIf)
		fmt.Println()

		fmt.Print("E = ")
		printMpf(Ef)
		fmt.Println()

		fmt.Print("NATLOGONEPOINTNINE = ")
		printMpf(NATLOGONEPOINTNINEf)
		fmt.Println()
	}

	var N big.Int
	_, err := fmt.Scan(&N)
	if err == nil {
		Atkin(&N)
	}
}
