----------------------------------------------------------------
--
-- aartifact
-- http://www.aartifact.org/src/
-- Copyright (C) 2008-2010
-- A. Lapets
--
-- This software is made available under the GNU GPLv3.
--
-- ContextOntology.hs
--   Concrete syntax of the propositions that constitute the
--   built-in ontology.

----------------------------------------------------------------
--

module ContextOntology where

  ont = "\\vbeg  Assume $0 \\in \\N$. Assume $1 > 0$. Assume $1 \\in \\N$. Assume $1$ is odd. Assume $2 > 1$. Assume $2 \\in \\N$. Assume $2$ is even. Assume $2$ is prime. Assume $\\emptyset$ is a finite set. Assume $\\emptyset$ is a finite set. Assume $\\emptyset$ is a finite set. Assume $\\emptyset$ is a set. Assume $\\N \\subset \\Z$. Assume $\\N$ is a set. Assume $\\N$ is an infinite set. Assume $\\nofix{*} \\in \\R \\times \\R \\rightarrow \\R$. Assume $\\nofix{+} \\in \\R \\times \\R \\rightarrow \\R$. Assume $\\Q \\subset \\R$. Assume $\\Q$ is a set. Assume $\\Q$ is an infinite set. Assume $\\R$ is a set. Assume $\\R$ is an infinite set. Assume $\\R$ is an uncountable set. Assume $\\Z \\subset \\Q$. Assume $\\Z$ is a set. Assume $\\Z$ is an infinite set. Assume $\\{0,1\\} \\subset \\N$. Assume considering $n/2$, $n$ is even implies $n/2 \\in \\Z$. Assume considering $x * y$, if $x$ is composite, $y \\in \\Z$, and $y \\neq 0$ then $x * y$ is composite. Assume considering $x * y$, if $y$ is composite, $x \\in \\Z$, and $x \\neq 0$ then $x * y$ is composite. Assume considering $X - Y$, $X$ is a set and $Y$ is a set implies $X - Y \\subseteq X$. Assume considering $X \\cap Y$, if $X$ is a set and $Y$ is a set then $X \\cap Y$ is a set. Assume considering $x \\cdot (y/x)$, $x \\in \\R$, $y \\in \\R$, and $x \\neq 0$ implies that $x \\cdot (y/x) = y$. Assume considering $x \\cdot y$, $x \\in Z$ and $y$ is even implies $x \\cdot y$ is even. Assume considering $x \\cdot y$, $x \\in \\N$  and $y \\in \\N$ implies that $x \\cdot y \\in \\N$. Assume considering $x \\cdot y$, $x \\in \\Q$  and $y \\in \\Q$ implies that $x \\cdot y \\in \\Q$. Assume considering $x \\cdot y$, $x \\in \\R$  and $y \\in \\R$  implies that $x \\cdot y \\in \\R$. Assume considering $x \\cdot y$, $x \\in \\Z$  and $y \\in \\Z$ implies that $x \\cdot y \\in \\Z$. Assume considering $x \\cdot y$, $x \\in \\Z$ and $y \\in \\Z$ implies \\l{$x$ is a factor of $x \\cdot y$} and \\l{$y$ is a factor of $x \\cdot y$}. Assume considering $x \\cdot y$, $x$ is even and $y \\in \\Z$ implies $x \\cdot y$ is even. Assume considering $x \\cdot y$, $x$ is even and $y$ is even implies that $x \\cdot y$ is even. Assume considering $x \\cdot y$, $x$ is even and $y$ is odd implies $x \\cdot y$ is even. Assume considering $x \\cdot y$, $x$ is negative and $y$ is negative implies $x \\cdot y$ is positive. Assume considering $x \\cdot y$, $x$ is negative and $y$ is positive implies $x \\cdot y$ is negative. Assume considering $x \\cdot y$, $x$ is odd and $y$ is even implies $x \\cdot y$ is even. Assume considering $x \\cdot y$, $x$ is odd and $y$ is odd implies $x \\cdot y$ is odd. Assume considering $x \\cdot y$, $x$ is positive and $y$ is negative implies $x \\cdot y$ is negative. Assume considering $x \\cdot y$, $x$ is positive and $y$ is positive implies $x \\cdot y$ is positive. Assume considering $X \\cup Y$, if $X$ is a set and $Y$ is a set then $X \\cup Y$ is a set. Assume considering $X \\rightarrow Y$, $X$ is a set and $Y$ is a set implies that $X \\rightarrow Y$ is a set. Assume considering $X \\times Y$, $X$ is a finite set and $Y$ is a finite set implies $X \\times Y$ is a finite set. Assume considering $X \\times Y$, $X$ is a finite set and $Y$ is a finite set implies $X \\times Y$ is a finite set. Assume considering $X \\times Y$, $X$ is a set and $Y$ is a set implies that $X \\times Y$ is a set. Assume considering $x+y$, $x \\in \\Q$  and $y \\in \\Q$  implies that $x + y \\in \\Q$. Assume considering $x+y$, $x \\in \\Z$  and $y \\in \\Z$ implies that $x + y \\in \\Z$. Assume considering $x+y$, $x$ is even and $y$ is even implies $x+y$ is even. Assume considering $x+y$, $x$ is even and $y$ is odd implies $x+y$ is odd. Assume considering $x+y$, $x$ is negative and $y$ is negative implies $x+y$ is negative. Assume considering $x+y$, $x$ is odd and $y$ is even implies $x+y$ is odd. Assume considering $x+y$, $x$ is odd and $y$ is odd implies $x+y$ is even. Assume considering $x+y$, $x$ is positive and $y$ is positive implies $x+y$ is positive. Assume considering $x+y$, if $x \\geq 0$ and $y \\geq 0$ then $x+y \\geq x$ and $x+y \\geq y$. Assume considering $x+y$, if $x \\in \\N$ and $y \\in \\N$ then $x+y \\in \\N$. Assume considering $x+y$, if $x \\in \\R$ and $y \\in \\R$ then $x+y \\in \\R$. Assume considering $x-y$, $x \\geq y$ implies that $x - y \\geq 0$. Assume considering $x-y$, $x \\in \\N$, $y \\in \\N$, and $x \\geq y$ implies $x-y \\in \\N$. Assume considering $x-y$, $x \\in \\Q$  and $y \\in \\Q$ implies that $x - y \\in \\Q$. Assume considering $x-y$, $x \\in \\Z$  and $y \\in \\Z$ implies that $x - y \\in \\Z$. Assume considering $X-Y$, $X$ is a set and $Y$ is a set implies $X - Y$ is a set. Assume considering $x/2$, $x \\in \\Z$ and $x$ is even implies $x/2 \\in \\Z$. Assume considering $x/y$, $x \\in \\Q$, $y \\in \\Q$, and $y \\neq 0$ implies that $x / y \\in \\Q$. Assume considering $x^y$, $x > 0$ and $y \\in \\R$ implies $x^y > 0$. Assume considering $x^y$, $x \\in \\Q$ and $y \\in \\Z$ implies that $x ^ y \\in \\Q$. Assume considering $x^y$, $x \\in \\Z$, $y \\in \\N$, $x^y$ is even implies $x$ is even. Assume considering $x^y$, $x$ is even, $y \\in \\N$, and $y > 0$ implies $x^y$ is even. Assume considering $x^y$, if $x \\in \\N$ and $y \\in \\N$ then $x^y \\in \\N$. Assume considering $x^y$, if $x \\in \\Z$ and $y \\in \\N$ then $x^y \\in \\Z$. Assume considering $x^y$, if $x \\in \\Z$ and $y \\in \\Z$ then \\l{$x^y$ is a power of $x$}. Assume considering $\\lceil x \\rceil$, $x \\in \\R$ implies that $\\lceil x \\rceil \\in \\Z$ and $\\lceil x \\rceil \\geq x$. Assume considering $\\lceil x \\rceil$, $x \\in \\Z$ implies that $\\lceil x \\rceil = x$. Assume considering $\\lfloor x \\rfloor$, $x \\in \\R$ implies that $\\lfloor x \\rfloor \\in \\Z$ and $\\lfloor x \\rfloor \\leq x$. Assume considering $\\lfloor x \\rfloor$, $x \\in \\Z$ implies that $\\lfloor x \\rfloor = x$. Assume considering $\\log x$, if $x > 0$ then $\\log x \\in \\R$. Assume considering $\\log_b x$, if $x > 0$ and $b > 0$ then $\\log_b x \\in \\R$. Assume considering $\\max S$, if $S$ is a finite set and $S \\subset \\R$ then $\\max S \\in S$. Assume considering $\\min S$, if $S$ is a finite set and $S \\subset \\R$ then $\\min S \\in S$. Assume considering $\\sqrt{x}$, $x \\in \\R$ and $x \\geq 0$ implies $\\sqrt{x} \\in \\R$. Assume considering $\\sqrt{x}^2$, $x \\in \\R$ and $x \\geq 0$ implies $\\sqrt{x}^2 = x$. Assume considering $\\sum_{x \\in S} x$, $S \\subset \\R$ and $S$ is a finite set implies \\l{$\\sum_{x \\in S} x$ is the sum of $S$}. Assume considering $\\{f(x) | x \\in \\dom f\\}$, if $f$ is a total function then $\\{f(x) | x \\in \\dom f\\} = \\ran f$. Assume considering $\\{i, ..., j\\}$, $i \\in \\N$, $j \\in \\N$, and $i \\leq j$ implies $\\{i, ..., j\\} \\subset \\N$. Assume considering $\\{i, ..., j\\}$, $i \\in \\Z$ and $j \\in \\Z$ and $i \\leq j$ implies that \\l{$\\{i, ..., j\\}$ is the set of integers from $i$ to $j$}. Assume considering $\\{i, ..., j\\}$, $i \\in \\Z$ and $j \\in \\Z$ implies that $\\{i, ..., j\\}$ is a finite set. Assume considering $\\{i, ..., j\\}$, $i \\in \\Z$, $j \\in \\Z$, and $j < i$ implies $\\{i, ..., j\\} = \\emptyset$. Assume considering $\\{v_i | i \\in \\{0,\\ldots,|v|-1\\}\\}$, if $v$ is a vector then \\l{$\\{v_i | i \\in \\{0,\\ldots,|v|-1\\}\\}$ is the set of components in $v$}. Assume considering $\\{v_k | k \\in \\{i,\\ldots,j\\}\\}$, $i \\in \\N$, $j \\in \\N$, $v$ is a vector with unbounded length, and $i \\leq j$ implies that \\l{$\\{v_k | k \\in \\{i,\\ldots,j\\}\\}$ is the set of components in $v$ ranging from $i$ to $j$}. Assume considering $\\{x | x \\in S\\}$, if $S$ is a set then $\\{x | x \\in S\\}$ is a set. Assume considering $\\{x\\}$, $\\{x\\}$ is a singleton. Assume considering $\\{x|x \\in S\\}$, $S$ is a set implies $\\{x|x \\in S\\} = S$. Assume considering $|x|$, if $x \\in \\Z$ then $|x| \\in \\N$. Assume for all $f,X,Y$, if $f \\in X \\rightarrow Y$ then $\\dom(f) \\subseteq X$, $\\ran(f) \\subseteq Y$, and $f$ is a map. Assume for all $i, j, X, k, l, Y$, $j \\geq k$ and \\l{$X$ is the set of integers from $i$ to $j$} and \\l{$Y$ is the set of integers from $k$ to $l$} implies that \\l{$X \\cup Y$ is the set of integers from $i$ to $l$}. Assume for all $V$, $V$ is a set implies that $V^\\ast$ is a set. Assume for all $v,V,i$, if \\l{$v$ is an infinite sequence of elements from $V$} and $i \\in \\N$ then $v \\in V^\\ast$. Assume for all $v,V,i$, if \\l{$v$ is an infinite sequence of elements from $V$} and $i \\in \\N$ then $v_i \\in V$. Assume for all $v,x$, if \\l{$x$ is a component of $v$} and $v$ are sets then $x$ is a set. Assume for all $x$, $x < 0$ iff $x$ is negative. Assume for all $x$, $x > 0$ iff $x$ is positive. Assume for all $x$, $x \\in \\N$ implies that $x \\geq 0$. Assume for all $x$, $x \\in \\Q$ iff $x$ is rational. Assume for all $x$, $x \\in \\R$ implies $x \\geq x$. Assume for all $x$, $x \\in \\R$ implies $x \\leq x$. Assume for all $x$, $x \\in \\Z$ and $x \\geq 0$ implies $x \\in \\N$. Assume for all $x$, $x \\neq 0$ iff $x$ is non-zero. Assume for all $x$, $x \\neq x$ implies there is a contradiction. Assume for all $X$, if $X$ is a set then $X \\subseteq X$. Assume for all $X$, if $X$ is a set then $\\emptyset \\subseteq X$. Assume for all $x$, if $x$ is even and $x$ is odd then there is a contradiction. Assume for all $X,x$, if \\l{$x$ is the sum of $X$} and $X \\subset \\N$ and $X$ is a finite set then $x \\in \\N$. Assume for all $x,X,Y$, if $x \\in X$ and $X \\subseteq Y$ then $x \\in Y$. Assume for all $x,X,y,Y$, if \\l{$x$ is the sum of $X$}, \\l{$y$ is the sum of $Y$}, $X \\subseteq Y$, and $Y \\subset \\N$ then $x \\leq y$. Assume for all $x,y$, $x < y$ iff $y > x$. Assume for all $x,y$, $x < y$ implies $x \\leq y$. Assume for all $x,y$, $x < y$ implies $x \\neq y$. Assume for all $x,y$, $x > y$ implies $x \\geq y$. Assume for all $x,y$, $x > y$ implies $x \\neq y$. Assume for all $x,y$, $x \\leq y$ and $x \\geq y$ implies $x = y$. Assume for all $x,y$, $x \\leq y$ iff $y \\geq x$. Assume for all $x,y$, if $x < y$ then $x - y < 0$. Assume for all $x,y$, if $x > y$ then $x - y > 0$. Assume for all $X,Y$, if $X \\subset Y$ then $X \\subseteq Y$. Assume for all $x,y,X,Y$, $x \\in X$ and $y \\in Y$ implies $(x,y) \\in X \\times Y$. Assume for all $x,y,z$, $x < y$ and $y < z$ implies $x < z$. Assume for all $x,y,z$, $x > y$ and $y > z$ implies $x > z$. Assume for all $x,y,z$, $x \\geq y$ and $y \\geq z$ implies $x \\geq z$. Assume for all $x,y,z$, $x \\leq y$ and $y \\leq z$ implies $x \\leq z$. Assume for all $X,Y,Z$, if $X \\subset Y$ and $Y \\subset Z$ then $X \\subset Z$. Assume for all $X,Y,Z$, if $X \\subset Y$ then $X \\subset Y \\cup Z$. Assume for all $X,Y,Z$, if $X \\subset Z$ then $X \\subset Y \\cup Z$. Assume for all $X,Y,Z$, if $X \\subseteq Y$ and $Y \\subseteq Z$ then $X \\subseteq Z$. Assume for all $X,Y,Z$, if $X \\subseteq Y$ then $X \\subseteq Y \\cup Z$. Assume for all $X,Y,Z$, if $X \\subseteq Z$ then $X \\subseteq Y \\cup Z$. Assume for any $a,b,c,d$, $a \\geq b$ and $c \\geq d$ implies $a+c \\geq b+d$. Assume for any $a,b,c,d$, if $a \\geq b$ and $c \\leq d$ then $a-c \\geq b-d$. Assume for any $f,g,X,Y,Z$, \\l{$f$ is a total function from $X$ to $Y$} and \\l{$g$ is a total function from $Y$ to $Z$} implies that \\l{$g \\circ f$ is a total function from $X$ to $Z$}. Assume for any $f,x,X,Y$, \\l{$f$ is a total function from $X$ to $Y$} and $x \\in X$ implies $f(x) \\in Y$. Assume for any $f,x,X,Y$, \\l{$f$ is a total map from $X$ to $Y$} and $x \\in X$ implies $f(x) \\in Y$. Assume for any $f,X,Y$, if \\l{$f$ is a total function from $X$ to $Y$} then $f$ is a total function. Assume for any $i,j,X,k,l,Y$, if \\l{$k$ is one more than $j$}, \\l{$X$ is the set of integers from $i$ to $j$}, and \\l{$Y$ is the set of integers from $k$ to $l$} then \\l{$X \\cup Y$ is the set of integers from $i$ to $l$}. Assume for any $i,j,X,k,l,Y$, if \\l{$X$ is the set of integers from $i$ to $j$}, \\l{$Y$ is the set of integers from $k$ to $l$}, $i \\leq k$, and $j \\geq l$ then $Y \\subseteq X$. Assume for any $m$, if $m$ is a map then $\\dom(m)$ is a set and $\\ran(m)$ is a set. Assume for any $R,X,Y$, $R \\subseteq X \\times Y$ implies that \\l{$R$ is a relation between $X$ and $Y$}. Assume for any $S$, if $S$ is an infinite set then $\\powerset(S)$ is an infinite set. Assume for any $S,v,i,j$, if \\l{$S$ is the set of components in $v$ ranging from $i$ to $j$} then $S$ is a finite set. Assume for any $v$, $v$ is an infinite sequence iff $v$ is a vector with unbounded length. Assume for any $v,i,j,X,S$, if \\l{$S$ is the set of components in $v$ ranging from $i$ to $j$} and $v \\in X^\\ast$ then $S \\subset X$. Assume for any $v,S,i,j,T,k,l$, if \\l{$S$ is the set of components in $v$ ranging from $i$ to $j$}, \\l{$T$ is the set of components in $v$ ranging from $k$ to $l$}, $i \\leq k$ and $j \\geq l$ then $T \\subseteq S$. Assume for any $x$, $x \\in \\emptyset$ implies that there is a contradiction. Assume for any $x$, $x \\in \\R$ implies $|x| \\geq 0$. Assume for any $X$, $X$ is a finite set iff $|X| \\in \\N$. Assume for any $x$, if $x \\in \\Z$ then \\l{$x$ is one more than $x-1$}. Assume for any $x$, if $x \\in \\Z$ then \\l{$x+1$ is one more than $x$}. Assume for any $X$, if $X$ is a finite set then $\\powerset(X)$ is a finite set. Assume for any $X,i,j$, if \\l{$X$ is the set of integers from $i$ to $j$} then $\\max X = j$. Assume for any $X,i,j$, if \\l{$X$ is the set of integers from $i$ to $j$} then $\\min X = i$. Assume for any $x,X$, if \\l{$x$ is the sum of $X$} and $X \\subset \\N$ then $x \\in \\N$. Assume for any $x,X$, if \\l{$x$ is the sum of $X$} and $X \\subset \\N$ then $x \\in \\N$. Assume for any $x,X$, if \\l{$x$ is the sum of $X$} and $X \\subset \\Z$ then $x \\in \\Z$. Assume for any $X,Y$, $X \\in \\powerset(Y)$ iff $X \\subseteq Y$. Assume for any $x,y$, $x$ is even, $y$ is even, and \\l{$x$ and $y$ are relatively prime} implies that there is a contradiction. Assume for any $x,y$, if $x \\in \\{y\\}$ then $x = y$. Assume for any $X,Y$, if $X$ is a finite set and $Y$ is a finite set then $X \\cup Y$ is a finite set. Assume for any $X,Y,i,j$, \\l{$X$ is the set of integers from $i$ to $j$} and  \\l{$Y$ is the set of integers from $i$ to $j$} implies $X = Y$. \\vend"

--eof