/* Copyright (c) 2021 The Connectal Project
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <string>
#include <map>

#if 0
Concatenate(Al, Ar)
    A = createAutomaton(Al.state + Ar.state, Al.delta + Ar.delta, Al.initial,
                                                                   Ar.final)
    for each state f_l in Al.final do
        for each edgeR in Ar.delta do
            if (edgeR.start in Ar.initial)
                A.delta += {f_l, edgeR.sigma, edgeR.destination}
                if (edgeR.start in Ar.final)
                    A.final += {f_l}
    return A


Choice(A1, A2)
    return createAutomaton(Al.state + Ar.state, Al.delta + Ar.delta,
                        Al.initial + Ar.initial, Al.final + Ar.final)


Fuse(Al, Ar)
    A = createAutomaton(Al.state + Ar.state, Al.delta + Ar.delta, Al.initial,
                                                                   Ar.final)
    for each edgeL in Al.delta do
        if (edgeL.destination in Al.final)
            for each edgeR in Ar.delta do
                if (edgeR.start in Ar.initial)
                    sigma = createRetrieve symbol in Sigma for edgeL.sigma & edgeR.sigma
                    if (EOE signal not in sigmas primary symbols)
                        A.delta += {edgeL.start, sigma, edgeR.destination}
    return A


CycleDelay(low, high, Al, Ar)
    originallow = low
    if (high == 0)
        A = Fuse(Al, Ar)
    else
        if (high != $)
            high -= 1
        if (low != 0)
            low -= 1
        A = Concatenate(Al, Concatenate(As(true[*low:high]), Ar))
        if (originallow == 0)
            A = Choice(Fuse(Al, Ar), A)
    return A


RangeRepeat(low, high, A)
    if (high == 0)
        return createAutomaton({q1}, {}, {q1}, {q1})
    else
        A1 = createAutomaton(A)
        for i = 2 to high do
            A1 = Concatenate(A1, A)
            if (i <= (high - low + 1))
               A1.initial += {s | s in A1.state, s in A.initial}
        if (low == 0)
            A1.final += A1.initial
        return A1


KleeneClosure(A)
    delta_1 = createTransitionRelation {}
    for each edge in A.delta do
        if (edge.d in A.final)
            for each state i in A.initial do
                delta_1 += {edge.s, edge.sigma, i}
    A.delta += delta_1
    A.final += A.initial
    return A


Intersect(A1, A2)
    A1 = WeakDeterminize(A1)
    A2 = WeakDeterminize(A2)
    //here |A1.initial| == |A2.initial| == 1
    //a label is an ordered pair(u, v) | u in A1.state, v in A2.state
    q = createState(i_1, i_2)
    A = createAutomaton({q}, {}, {q}, 0)
    C = {q}                    // C is "to-construct"
    while (C.size()) do
        remove a state r (with label (u, v)), from C
        if (u in A1.final && v in A2.final)
            A.final += {r}
        for each edge1 in A1.delta do
            if (edge1.start == u)
                for each edge2 in A2.delta do
                    if (edge2.start == v)
                        find state t in A.state with label (edge1.distination, edge2.destination)
                        if not exists t
                            t = createState(edge1.distination, edge2.destination)
                            C += {t}
                        sigma = createRetrieve symbol in Sigma for edge1.sigma & edge2.sigma
                        delta += {r, sigma, t}
    return A


FirstFail(A)
    if ((I & F) != {})
        return createAutomaton({q1}, {}, {q1}, {})
    else
        A1 = StrongDeterminize(A)
        add a new state failState in A1.state
        for each state currentState in A1.state - {failState} do
            P = create set of primary symbols()
            for each edge in A1.delta do
                if (edge.s == currentState)
                    P += edge.sigmas primary symbols(s)
            if (P != {})
                for each assignment omega of primary symbols in P do
                    if (not exists(s, sigma, d) in A1.delta | s = currentState,
                                                      (sigma)omega = true)
                        sigma = createRetrieve symbol in Sigma for omega
                        A1.delta += {currentState, sigma, failState}
            else
                sigma = createRetrieve symbol in Sigma for true
                A1.delta += {currentState, sigma, failState}
        remove all edgeJ in A1.delta for which edgeJ.destination in A1.final
        A1.final = {failState}
        return A1   // |A1.final| <= 1, as required for FirstFailStrong

FirstMatch(A)
    A = StrongDeterminize(A)
    remove all edges (s_j, sigma_j, d_j) in A.delta | s_j in A.final
    return A

----------------------------------------------------------------------


Sequence
--------
s1 ##[i:j] s2:		CycleDelay(i, j, s1, s2)
s1 ##[i:$] s2:		CycleDelay(i, -1, s1, s2)
b/s[*i:j]:		RangeRepeat(i, j, b/s)
b/s[*i:$]:		Concatenate(RangeRepeat(i,i,b/s), KleeneClosure(b/s))
s1 intersect s2:	Intersect(s1, s2)
p/s1 or p/s2:		Choice(p/s1, p/s2)
first_match(s):		FirstMatch(s)

Property
--------
not p:			Complement(p)
s |-> p:		Choice(Complement(p), Fuse(s, p))
disable iff(b) p:	AddLiteral(p, !b)

Complement Property:
s:			FirstFail(s)
not p:			p
p1 or p2:		Complement(p1) && Complement(p2)
p1 and p2:		Complement(p1) || Complement(p2)
s |-> p:		Fuse(s, Complement(p))
disable iff(b) p:	AddLiteral(Complement(p), !b)

Statements
----------
assert property (@(clock_expr) p); :	Fuse(true [*1:$], Complement(p))
cover property (@(clock_expr) p); :	Cover(p)

#endif
