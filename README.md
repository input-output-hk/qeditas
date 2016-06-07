# qeditas
A Formal Library as a Bitcoin Spin-Off

qeditas.org

Qeditas is currently in its alpha development stage. Current versions
can be compiled (under linux).  The executable can only be run in
testnet mode. A console allows a limited number of commands to be
given. For example, addresses can be imported into a wallet and the
assets from the initial distribution can be viewed. There is not yet
a network.

* Installation

./configure
make

Instead of make, it is also possible to use the makebytecode script:

./configure
./makebytecode

* Running

./bin/qeditas -testnet

Without the initial ledger tree, there is little sensible to do except exit.

> exit

* Obtaining the Initial Ledger Tree

The initial ledger tree contains the initial distribution
of Qeditas assets (at least for the testnet)
and has hash root 66c029f4c29b351785c0480cedc9449b64332dfa.

The full tree is available as the file qeditas-db-initdistr-full.tgz
(656MB) at:
https://mega.nz/#!Ap5ylL4C!WLy3bTvMWSwuIKVQvmW7BOT7t38WWLeU8bVlRxt7CtE

To check the integrity, check the sha256sum is
6687d1f4bd4a6c2263276e83f6a27f3d7df465f8adfaa6322f950cb9ae58faf4

There are also two partial trees available.

If you are only interested in p2pkh (pay-to-public-key-hash)
addresses, the slightly smaller file
qeditas-db-initdistr-p2pkhonly.tgz (606MB) is sufficient:
https://mega.nz/#!t5YnjJBZ!1LUVDNm9p7PYI51bA2__m323zwnBK3aG0r82_sGY7Qs

To check the integrity, check the sha256sum is
d48201961b2d2b904b1aad5911131d3f23714ac30d25daa085e9d45850afdded

If you are only interested in p2sh (pay-to-script-hash) addresses, the
much smaller file qeditas-db-initdistr-p2shonly.tgz (39MB) is
sufficient:

https://mega.nz/#!NlpTSY5I!eg2MYZeKLF0W30yngBlXprqrMnmqfz_Mx3QKOtIrjO0

To check the integrity, check the sha256sum is
fc3c39f7b87de31f9c4b46dfce2eeec0e1691bb7863455311ec3e8a875f06134

Whichever file you download, cd to the testnet subdirectory of your Qeditas data directory.
Most likely this mean:

cd ~/.qeditas/testnet

Move the downloaded file to here and untar it. For example:

tar xzvf qeditas-db-initdistr-full.tgz

It will create a db subdirectory with all the necessary information.

* Importing Watch Addresses and Viewing Balances

Here is an example of how to view assets from the initial distribution.
This assumes you have a version of the initial ledger tree (see above).

We first import 3 p2pkh addresses and one p2sh address. We give them
as Bitcoin addresses and Qeditas prints the corresponding Qeditas address.
Qeditas p2pkh addresses start with Q. Qeditas p2sh addresses start with q.

> importwatchbtcaddr 14M2d3UDXkkTL8AJmTUifUmAEwYo67cW2Q
Importing as Qeditas address QPx1jLkviDdGmGFLBnoCnkYnkCVWM71btK
> importwatchbtcaddr 1LvNDhCXmiWwQ3yeukjMLZYgW7HT9wCMru
Importing as Qeditas address QgXMKzVExBPkqC4gL63qTqLK1NEAMsuzcq
> importwatchbtcaddr 15muB9t6z5UZBCWTkTApgEUYnMZdcnumKo
Importing as Qeditas address QRNtHTApAYMNcLbVAnVJoWGBHcWLwur5vQ
> importwatchbtcaddr 37GxXLE4tiFEKwsLzNGFdHyjVfUEbj6wt2
Importing as Qeditas address qP9KkpWCYTXzNnuJocZuPiHCsg6iKXzhyn

We next ask Qeditas to print the assets. The initial ledger root
66c029f4c29b351785c0480cedc9449b64332dfa is the default ledger root
for now. In the future, the default ledger root will be the ledger
root of the best block.

> printassets
Assets in ledger with root 66c029f4c29b351785c0480cedc9449b64332dfa:
Controlled p2pkh assets:
Possibly controlled p2sh assets:
Assets via endorsement:
Watched assets:
QPx1jLkviDdGmGFLBnoCnkYnkCVWM71btK:
0d5edd430a4ffe63fa96dd5c189989bd39b628cb [0] Currency 10000000000
QgXMKzVExBPkqC4gL63qTqLK1NEAMsuzcq:
37cfcd67a77ded709ff0b03c1d80ed5fbed8b33f [0] Currency 150000000
QRNtHTApAYMNcLbVAnVJoWGBHcWLwur5vQ:
3b522a6135a10dff029666431e145aa4a2d0e824 [0] Currency 150000000
qP9KkpWCYTXzNnuJocZuPiHCsg6iKXzhyn:
ab6f7c6f2d94d3f7a36f39c64b46f4f6d5b492d0 [0] Currency 150000000

For each of the imported addresses, there is a currency asset.

By Bitcoin Block 350,000

14M2d3UDXkkTL8AJmTUifUmAEwYo67cW2Q had a balance of 0.1 bitcoins (10000000 satoshis)

Hence the corresponding Qeditas address
QPx1jLkviDdGmGFLBnoCnkYnkCVWM71btK has 0.1 fraenks (10000000000 cants).
The number of cants is 1000 times more than the number of satoshis
since Qeditas has three extra digits of precision.

Similarly, by Bitcoin Block 350,000 the addresses
1LvNDhCXmiWwQ3yeukjMLZYgW7HT9wCMru, 15muB9t6z5UZBCWTkTApgEUYnMZdcnumKo
and 37GxXLE4tiFEKwsLzNGFdHyjVfUEbj6wt2 had balances of 0.0015 bitcoins
(150000 satoshis).  Consequently, the corresponding Qeditas addresses
QgXMKzVExBPkqC4gL63qTqLK1NEAMsuzcq, QRNtHTApAYMNcLbVAnVJoWGBHcWLwur5vQ
and qP9KkpWCYTXzNnuJocZuPiHCsg6iKXzhyn have 0.0015 fraenks
(150000000 cants) each.

Note: If you download one of the smaller files approximating the
initial ledger tree, Qeditas may warn you that some data is missing as
follows:

Warning: The complete ledger is not in the local database and there are no connections to request missing data.
