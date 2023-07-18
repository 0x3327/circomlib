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
    MultiMux1 takes in an n-array of 2 constants as an input and a selector.
    A selector chooses first or the second constant from each row.
    Notice that a selector can only choose all constants at first or second position.
    It cannot choose constant at position 0 of the first row and then constant at position 1 from some other row. 

    argument n - length of a 2-constant array
    input c[n][2] - n rows of 2 constants
    input s - selector (0 or 1)
    output out[n] - n outputs of the constants that have been selected
*/
template MultiMux1(n) {
    signal input c[n][2];  // Constants
    signal input s;   // Selector
    signal output out[n];

    for (var i=0; i<n; i++) {

        out[i] <== (c[i][1] - c[i][0])*s + c[i][0];

    }
}

/*
    Mux1 takes 2 constants as inputs, and a selector.
    The output is the constant that is selected by the selector.

    input c[2] - 2 constants to select from
    input s - selector (0 or 1)
    output out - the constant that has been selected
*/
template Mux1() {
    var i;
    signal input c[2];  // Constants
    signal input s;   // Selector
    signal output out;

    component mux = MultiMux1(1);

    for (i=0; i<2; i++) {
        mux.c[0][i] <== c[i];
    }

    s ==> mux.s;

    mux.out[0] ==> out;
}
