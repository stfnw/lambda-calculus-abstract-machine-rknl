<!--
SPDX-FileCopyrightText: 2022 Paper and original Racket Code: Małgorzata Biernacka, Witold Charatonik, and Tomasz Drab. 2022. A simple and efficient implementation of strong call by need by an abstract machine. Proc. ACM Program. Lang. 6, ICFP, Article 94 (August 2022), 28 pages. https://doi.org/10.1145/3549822
SPDX-License-Identifier: CC-BY-4.0

SPDX-FileCopyrightText: 2026 This specific implementation: Stefan Walter (stfnw)
SPDX-License-Identifier: MIT
-->

This iteration/version of RKNL is a direct implementation of the paper in Rust.
Compared to the previous iteration it supports an optimization: reference counting of Locations.
I.e. the Store mapping from Locations to StorableValues is garbage collected:
entries are removed once Locations are not referenced anymore in the other data structures.
