import org.checkerframework.checker.dividebyzero.qual.*;

// Another simple test case for my divide-by-zero checker.
// The file contains "// ::" comments to indicate expected
// errors and warnings; see
// https://github.com/typetools/checker-framework/blob/master/checker/tests/README.

// Adds a few tests for remainder and to see what happens if we use an 
// erroneous variable anyway.
class Bar {

    public static void f() {
        int one  = 1;
        int zero = 0;
        // :: error: divide.by.zero
        int x    = one % zero;

        // It looks like "top" is the correct type for an erroneous value if we want prior errors to act like "any value" later in the program.
        // :: error: divide.by.zero
        int q = 1 / x;

        int y    = zero % one;
        // :: error: divide.by.zero
        int z    = x % y;
        String s = "hello";
    }

    public static void g(int y) {
        if (y == 0) {
            // :: error: divide.by.zero
            int x = 1 % y;
        } else {
            int x = 1 / y;
        }

        if (y != 0) {
            int x = 1 / y;
        } else {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (!(y == 0)) {
            int x = 1 / y;
        } else {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (!(y != 0)) {
            // :: error: divide.by.zero
            int x = 1 / y;
        } else {
            int x = 1 / y;
        }

        if (y < 0) {
            int x = 1 / y;
        }

        if (y <= 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (y > 0) {
            int x = 1 / y;
        }

        if (y >= 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        }
    }

    public static void h() {
        int zero_the_hard_way = 0 + 0 - 0 * 0;
        // :: error: divide.by.zero
        int x = 1 / zero_the_hard_way;

        int one_the_hard_way = 0 * 1 + 1;
        int y = 1 / one_the_hard_way;
    }

    public static void l() {
        // :: error: divide.by.zero
        int a = 1 / (1 - 1);
        int y = 1;
        // :: error: divide.by.zero
        int x = 1 / (y - y);
        int z = y-y;
        // :: error: divide.by.zero
        int k = 1/z;
    }

    public static void safeAddition() {
        // both positive
        int a = 1 / (2 + 3);

        // both negative
        int b = -1 / (-4 + -6);
    }

    public static void safeSubtraction() {
        // negative minus a postive isn't zero
        int a = 1 / (-3 - 4);

        // positive minus a negative isn't zero
        int b = -5;
        int c = 10 / (1 - b);
    }

    public static void multiplicationPreservesSigns() {

        int a = 1 * 2;
        int b = 3 + a;
        int c = -1 / b;

        int d = 1 * -3;
        int e = 3 + d;
        // :: error: divide.by.zero
        int f = 2 / e;
    }

    public static void complicatedSafeSequence() {
        int c = 3;
        c += 5;
        c *= (2 + 1);
        c *= (-3 * -4);
        c += 1;
        int d = 1 % c;
    }

    public static void modAssignment() {
        int a = 3;
        // :: error: divide.by.zero
        a %= 0;

        int c = 4;
        c %= 4;

        // :: error: divide.by.zero
        int d = 1 % c;

        int b = 10;
        // :: error: divide.by.zero
        b %= (3 * 0);
    }

}
