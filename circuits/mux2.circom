/*
    Copyright 2018 0KIMS association.

    This file is part of circom (Zero Knowledge Circuit Compiler).

    circom is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    circom is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with circom. If not, see <https://www.gnu.org/licenses/>.
*/
pragma circom 2.0.0;

/*
    MultiMux2 takes in an n-array of 4 constants as an input and a selector.
    A selector chooses one of the 4 constants from each row.
    Notice that a selector can only choose all constants at the same position.
    It cannot choose constant at position 0 of the first row and then constant at position 2 from some other row. 

    argument n - length of a 4-constant array
    input c[n][4] - n rows of 4 constants
    input s[2] - selector (0 to 3 in bits)
    output out[n] - n outputs of the constants that have been selected
*/
template MultiMux2(n) {
    signal input c[n][4];  // Constants
    signal input s[2];   // Selector
    signal output out[n];

    signal a10[n];
    signal a1[n];
    signal a0[n];
    signal a[n];

    signal  s10;
    s10 <== s[1] * s[0];

    for (var i=0; i<n; i++) {

          a10[i] <==  ( c[i][ 3]-c[i][ 2]-c[i][ 1]+c[i][ 0] ) * s10;
           a1[i] <==  ( c[i][ 2]-c[i][ 0] ) * s[1];
           a0[i] <==  ( c[i][ 1]-c[i][ 0] ) * s[0];
            a[i] <==  ( c[i][ 0] );

          out[i] <==  (  a10[i] +  a1[i] +  a0[i] +  a[i] );

    }
}

/*
    Mux2 takes 4 constants as inputs, and a selector.
    The output is the constant that is selected by the selector.

    input c[4] - 4 constants to select from
    input s[2] - selector (0 to 3 in bits)
    output out - the constant that has been selected
*/
template Mux2() {
    var i;
    signal input c[4];  // Constants
    signal input s[2];   // Selector
    signal output out;

    component mux = MultiMux2(1);

    for (i=0; i<4; i++) {
        mux.c[0][i] <== c[i];
    }

    for (i=0; i<2; i++) {
      s[i] ==> mux.s[i];
    }

    mux.out[0] ==> out;
}
