<!--
SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
SPDX-License-Identifier: CC-BY-4.0

SPDX-FileCopyrightText: 2026 This specific implementation: Stefan Walter (stfnw)
SPDX-License-Identifier: MIT
-->

# Experimenting with the RKNL abstract machine

This repository contains some example code I wrote while working through the following paper (unaffiliated) and experimenting with the topic:
Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab, "A simple and efficient implementation of strong call by need by an abstract machine", Proc. ACM Program. Lang., vol. 6, no. ICFP, pp. 109–136, Aug. 2022, doi: 10.1145/3549822 (licensed CC-BY-4.0).
The accompanying code was also helpful: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022a. Abstract Machines Workshop, https://zenodo.org/records/6786796 (Code, mainly in Racket, licensed CC-BY-4.0)

The repository implements the RKNL abstract machine for reducing/evaluation untyped lambda calculus terms.
It contains several slightly different versions / iterations; each variation is described further in their own README.

Goal is me learning; this project will probably not be maintained further.
Motivation is better understanding strong / full reduction (i.e. inside lambda abstractions, reducing according to normal order evaluation strategy),
while also memoizing / sharing already computed results and not performing unnecessary duplicate term-reductions (call-by-need / lazy evaluation).

I found said paper to very clearly describe an abstract machine for this evaluation strategy that can directly be implemented in code.
Another very good read for categorization of different reduction strategies and their implementation in abstract machines, that also gives more context around this topic, is the corresponding Ph. D. Dissertation:
Tomasz Drab, "Reduction Strategies in the Lambda Calculus and Their Implementation through Derivable Abstract Machines", University of Wrocław Faculty of Mathematics and Computer Science, Sep. 2022, Online. Available: https://bip.uni.wroc.pl/download/attachment/37818/rozprawa-doktorska.pdf .
Its introduction is also published as: Introduction from T. Drab, "Reduction Strategies in the Lambda Calculus and Their Implementation through Derivable Abstract Machines: Introduction", May 21, 2024, arXiv: arXiv:2405.12586. doi: 10.48550/arXiv.2405.12586.

Therein, e.g. Table 2 "Selected abstract machines" gives an overview over some existing abstract machines; relevant here for strong / full-reducing abstract machines are for example:
- KN, which can have exponential overhead for certain lambda terms, and
- RKNL, which has polynomial (bilinear in the number of $\beta$-reductions and the initial term size) overhead (due to sharing / call-by-need)

The state transition rules for the RKNL abstract machine itself are listed in Table 1 "The RKNL abstract machine, a reasonable and lazy variant of KN".
