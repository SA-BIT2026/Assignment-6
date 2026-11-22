/**
 * verify.cpp
 * @author kisslune
 */

#include "Z3Mgr.h"

using namespace z3;
using namespace SVF;


/* A simple example

int main() {
    int* p;
    int q;
    int* r;
    int x;

    p = malloc();
    q = 5;
    *p = q;
    x = *p;
    assert(x==5);
}
*/
void Z3Tests::test0()
{
    //  int* p;
    expr p = getZ3Expr("p");
    //  int q;
    expr q = getZ3Expr("q");
    //  int* r;
    expr r = getZ3Expr("r");
    //  int x;
    expr x = getZ3Expr("x");
    //  p = malloc();
    addToSolver(p == getMemObjAddress("malloc"));
    //  q = 5;
    addToSolver(q == 5);
    //  *p = q;
    storeValue(p, q);
    //  x = *p;
    addToSolver(x == loadValue(p));

    // print the expression values
    printExprValues();

    addToSolver(x == getZ3Expr(10));
    // print the result of satisfiability check
    std::cout << solver.check() << std::endl;
}


/*
// Simple integers

    int main() {
        int a;
        int b;
        a = 0;
        b = a + 1;
        assert(b > 0);
    }
*/
void Z3Tests::test1()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    addToSolver(a == getZ3Expr(0));
    addToSolver(b == a + getZ3Expr(1));
    printExprValues();
    std::cout << checkNegateAssert(b > getZ3Expr(0)) << std::endl;
}


/*
  // One-level pointers

    int main() {
        int* p;
        int q;
        int b;
        p = malloc;
        *p = 0;
        q = *p;
        *p = 3;
        b = *p + 1;
        assert(b > 3);
    }
*/
void Z3Tests::test2()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr b = getZ3Expr("b");
    addToSolver(p == getMemObjAddress("malloc"));
    storeValue(p, getZ3Expr(0));
    addToSolver(q == loadValue(p));
    storeValue(p, getZ3Expr(3));
    addToSolver(b == loadValue(p) + getZ3Expr(1));
    printExprValues();
    std::cout << checkNegateAssert(b > getZ3Expr(3)) << std::endl;
}


/*
    // Mutiple-level pointers

    int main() {
        int** p;
        int* q;
        int* r;
        int x;

        p = malloc1(..);
        q = malloc2(..);
        *p = q;
        *q = 10;
        r = *p;
        x = *r;
        assert(x==10);
    }
*/
void Z3Tests::test3()
{
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr x = getZ3Expr("x");
    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(q == getMemObjAddress("malloc2"));
    storeValue(p, q);
    storeValue(q, getZ3Expr(10));
    addToSolver(r == loadValue(p));
    addToSolver(x == loadValue(r));
    printExprValues();
    std::cout << checkNegateAssert(x == getZ3Expr(10)) << std::endl;
}


/*
   // Array and pointers

    int main() {
        int* p;
        int* x;
        int* y;
        int a;
        int b;
        p = malloc;
        x = &p[0];
        y = &p[1]
        *x = 10;
        *y = 11;
        a = *x;
        b = *y;
        assert((a + b)>20);
    }
*/
void Z3Tests::test4()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    addToSolver(p == getMemObjAddress("malloc"));
    addToSolver(x == getGepObjAddress(p, 0));
    addToSolver(y == getGepObjAddress(p, 1));
    storeValue(x, getZ3Expr(10));
    storeValue(y, getZ3Expr(11));
    addToSolver(a == loadValue(x));
    addToSolver(b == loadValue(y));
    printExprValues();
    std::cout << checkNegateAssert(a + b > getZ3Expr(20)) << std::endl;
}


/*
    // Branches

int main(int argv) {
    int a;
    int b;
    int b1;
    a = argv + 1;
    b = 5;
    if(a > 10)
        b = a;
    b1 = b;
    assert(b1 >= 5);
}
*/
void Z3Tests::test5()
{
    expr argv = getZ3Expr("argv");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr b1 = getZ3Expr("b1");
    addToSolver(a == argv + getZ3Expr(1));
    // b is 5 on the false path and a on the true path
    addToSolver(b == ite(a > getZ3Expr(10), a, getZ3Expr(5)));
    addToSolver(b1 == b);
    printExprValues();
    std::cout << checkNegateAssert(b1 >= getZ3Expr(5)) << std::endl;
}


/*
// Compare and pointers
int main() {
   int *a = malloc1;
   int *b = malloc2;
   *a = 5;
   *b = 10;
   int *p;
   if (*a < *b) {
       p = a;
   } else {
       p = b;
   }
   assert(*p == 5);
}
*/
void Z3Tests::test6()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr p = getZ3Expr("p");
    addToSolver(a == getMemObjAddress("malloc1"));
    addToSolver(b == getMemObjAddress("malloc2"));
    storeValue(a, getZ3Expr(5));
    storeValue(b, getZ3Expr(10));
    addToSolver(p == ite(loadValue(a) < loadValue(b), a, b));
    printExprValues();
    std::cout << checkNegateAssert(loadValue(p) == getZ3Expr(5)) << std::endl;
}


/*
 int main() {
	int a = 1, b = 2, c = 3;
	int d;
  if (a > 0) {
  	d = b + c;
  }
  else {
  	d = b - c;
  }
  assert(d == 5);
 }
 */
void Z3Tests::test7()
{
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr c = getZ3Expr("c");
    expr d = getZ3Expr("d");
    addToSolver(a == getZ3Expr(1));
    addToSolver(b == getZ3Expr(2));
    addToSolver(c == getZ3Expr(3));
    addToSolver(d == ite(a > getZ3Expr(0), b + c, b - c));
    printExprValues();
    std::cout << checkNegateAssert(d == getZ3Expr(5)) << std::endl;
}


/*
 int main() {
    int arr[2] = {0, 1};
    int a = 10;
    int *p;
    if (a > 5) {
        p = &arr[0];
    }
    else {
        p = &arr[1];
    }
    assert(*p == 0);
 }
 */
void Z3Tests::test8()
{
    expr arr = getZ3Expr("arr");
    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");
    addToSolver(arr == getMemObjAddress("arr"));
    expr first = getGepObjAddress(arr, 0);
    expr second = getGepObjAddress(arr, 1);
    storeValue(first, getZ3Expr(0));
    storeValue(second, getZ3Expr(1));
    addToSolver(a == getZ3Expr(10));
    addToSolver(p == ite(a > getZ3Expr(5), first, second));
    printExprValues();
    std::cout << checkNegateAssert(loadValue(p) == getZ3Expr(0)) << std::endl;
}


/*
    // Struct and pointers

    struct A{ int f0; int* f1;};
    int main() {
       struct A* p;
       int* x;
       int* q;
       int** r;
       int* y;
       int z;

       p = malloc1;
       x = malloc2;
       *x = 5;
       q = &(p->f0);
       *q = 10;
       r = &(p->f1);
       *r = x;
       y = *r;
       z = *q + *y;
       assert(z == 15);
    }
*/
void Z3Tests::test9()
{
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr y = getZ3Expr("y");
    expr z = getZ3Expr("z");
    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(x == getMemObjAddress("malloc2"));
    storeValue(x, getZ3Expr(5));
    addToSolver(q == getGepObjAddress(p, 0));
    storeValue(q, getZ3Expr(10));
    addToSolver(r == getGepObjAddress(p, 1));
    storeValue(r, x);
    addToSolver(y == loadValue(r));
    addToSolver(z == loadValue(q) + loadValue(y));
    printExprValues();
    std::cout << checkNegateAssert(z == getZ3Expr(15)) << std::endl;
}


/*
int foo(int z) {
    k = z;
    return k;
}
int main() {
  int x;
  int y;
  y = foo(2);
  x = foo(3);
  assert(x == 3 && y == 2);
}
*/
void Z3Tests::test10()
{
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    // each call needs its own version of k, otherwise the two assignments
    // to the global would be merged into an inconsistent constraint
    expr kFirst = getZ3Expr("k_first");
    expr kSecond = getZ3Expr("k_second");
    addToSolver(kFirst == getZ3Expr(2));
    addToSolver(y == kFirst);
    addToSolver(kSecond == getZ3Expr(3));
    addToSolver(x == kSecond);
    printExprValues();
    std::cout << checkNegateAssert(x == getZ3Expr(3) && y == getZ3Expr(2)) << std::endl;
}


int main()
{
    Z3Tests tests;
    tests.test0();
    tests.solver.reset();
    tests.test1();
    tests.solver.reset();
    tests.test2();
    tests.solver.reset();
    tests.test3();
    tests.solver.reset();
    tests.test4();
    tests.solver.reset();
    tests.test5();
    tests.solver.reset();
    tests.test6();
    tests.solver.reset();
    tests.test7();
    tests.solver.reset();
    tests.test8();
    tests.solver.reset();
    tests.test9();
    tests.solver.reset();
    tests.test10();

    return 0;
}
