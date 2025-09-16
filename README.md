# Fairy-Stockfish

## Overview

[![Build Status](https://github.com/fairy-stockfish/Fairy-Stockfish/actions/workflows/release.yml/badge.svg?branch=master)](https://github.com/fairy-stockfish/Fairy-Stockfish/actions?query=workflow%3ARelease)
[![Build Status](https://github.com/fairy-stockfish/Fairy-Stockfish/actions/workflows/fairy.yml/badge.svg?branch=master)](https://github.com/fairy-stockfish/Fairy-Stockfish/actions?query=workflow%3Afairy)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/fairy-stockfish/Fairy-Stockfish?branch=master&svg=true)](https://ci.appveyor.com/project/ianfab/Fairy-Stockfish/branch/master)
[![PyPI version](https://badge.fury.io/py/pyffish.svg)](https://badge.fury.io/py/pyffish)
[![NPM version](https://img.shields.io/npm/v/ffish.svg?sanitize=true)](https://www.npmjs.com/package/ffish)

Fairy-Stockfish is a chess variant engine derived from [Stockfish](https://github.com/official-stockfish/Stockfish/) designed for the support of fairy chess variants and easy extensibility with more games. It can play various regional, historical, and modern chess variants as well as [games with user-defined rules](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Variant-configuration). For [compatibility with graphical user interfaces](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Graphical-user-interfaces) it supports the UCI, UCCI, USI, UCI-cyclone, and CECP/XBoard protocols.

The goal of the project is to create an engine supporting a large variety of chess-like games, equipped with the powerful search of Stockfish. Despite its generality the [playing strength](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Playing-strength) is on a very high level in almost all supported variants. Due to its multi-protocol support Fairy-Stockfish works with almost any chess variant GUI.

## Installation
You can download the [Windows executable](https://github.com/fairy-stockfish/Fairy-Stockfish/releases/latest/download/fairy-stockfish-largeboard_x86-64.exe) or [Linux binary](https://github.com/fairy-stockfish/Fairy-Stockfish/releases/latest/download/fairy-stockfish-largeboard_x86-64) from the [latest release](https://github.com/fairy-stockfish/Fairy-Stockfish/releases/latest) or [compile the program from source](https://github.com/fairy-stockfish/Fairy-Stockfish#compiling-stockfish-yourself-from-the-sources). The program comes without a graphical user interface, so you perhaps want to use it together with a [compatible GUI](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Graphical-user-interfaces), or [play against it online](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Online) at [pychess](https://www.pychess.org/), [lishogi](https://lishogi.org/@/Fairy-Stockfish), or [lichess](https://lichess.org/@/Fairy-Stockfish). Read more about [how to use](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Usage) Fairy-Stockfish in the wiki.

If you want to preview the functionality of Fairy-Stockfish before downloading, you can try it out on the [Fairy-Stockfish playground](https://fairyground.vercel.app/) in the browser.

Optional NNUE evaluation parameter files to improve playing strength for many variants are in the [list of NNUE networks](https://fairy-stockfish.github.io/nnue/#current-best-nnue-networks).
For the regional variants Xiangqi, Janggi, and Makruk [dedicated releases with built-in NNUE networks](https://github.com/fairy-stockfish/Fairy-Stockfish-NNUE) are available. See the [wiki](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/NNUE) for more details on NNUE.

## Contributing

If you like this project, please support its development via [patreon](https://www.patreon.com/ianfab), [paypal](https://paypal.me/FairyStockfish), or [github](https://github.com/sponsors/ianfab), or by [contributing to the code](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Contributing) or documentation. An [introduction to the code base](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Understanding-the-code) can be found in the wiki.

## Supported games

The games currently supported besides chess are listed in [our variants page](https://fairy-stockfish.github.io/variants/). Fairy-Stockfish can also play user-defined variants loaded via a variant configuration file, see the file [`src/variants.ini`](https://github.com/ianfab/Fairy-Stockfish/blob/master/src/variants.ini) and the [wiki](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Variant-configuration).

## Help

See the [Fairy-Stockfish Wiki](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki) for more info, or if the required information is not available, open an [issue](https://github.com/fairy-stockfish/Fairy-Stockfish/issues) or join our [discord server](https://discord.gg/FYUGgmCFB4).

## Bindings

Besides the C++ engine, this project also includes bindings for other programming languages in order to be able to use it as a library for chess variants. They support move, SAN, and FEN generation, as well as checking of game end conditions for all variants supported by Fairy-Stockfish. Since the bindings are using the C++ code, they are very performant compared to libraries directly written in the respective target language.

### Python

The python binding [pyffish](https://pypi.org/project/pyffish/) contributed by [@gbtami](https://github.com/gbtami) is implemented in [pyffish.cpp](https://github.com/fairy-stockfish/Fairy-Stockfish/blob/master/src/pyffish.cpp). It is e.g. used in the backend for the [pychess server](https://github.com/gbtami/pychess-variants).

### Javascript

The javascript binding [ffish.js](https://www.npmjs.com/package/ffish) contributed by [@QueensGambit](https://github.com/QueensGambit) is implemented in [ffishjs.cpp](https://github.com/fairy-stockfish/Fairy-Stockfish/blob/master/src/ffishjs.cpp). The compilation/binding to javascript is done using emscripten, see the [readme](https://github.com/fairy-stockfish/Fairy-Stockfish/tree/master/tests/js).

## Ports

### WebAssembly

For in-browser use a [port of Fairy-Stockfish to WebAssembly](https://github.com/fairy-stockfish/fairy-stockfish.wasm) is available at [npm](https://www.npmjs.com/package/fairy-stockfish-nnue.wasm). It is e.g. used for local analysis on [pychess.org](https://www.pychess.org/analysis/chess). Also see the [Fairy-Stockfish WASM demo](https://github.com/ianfab/fairy-stockfish-nnue-wasm-demo) available at https://fairy-stockfish-nnue-wasm.vercel.app/.

## Other resources

Please see [the Official Stockfish wiki](https://github.com/official-stockfish/Stockfish/wiki) for base information about Stockfish,
then [the Fairy Stockfish wiki](https://github.com/fairy-stockfish/Fairy-Stockfish/wiki) for information about how Fairy Stockfish differs.

## Terms of use

Fairy Stockfish is free, and distributed under the **GNU General Public License version 3**
(GPL v3). Essentially, this means you are free to do almost exactly
what you want with the program, including distributing it among your
friends, making it available for download from your website, selling
it (either by itself or as part of some bigger software package), or
using it as the starting point for a software project of your own.

The only real limitation is that whenever you distribute Fairy Stockfish in
some way, you MUST always include the full source code, or a pointer
to where the source code can be found, to generate the exact binary
you are distributing. If you make any changes to the source code,
these changes must also be made available under the GPL.

For full details, read the copy of the GPL v3 found in the file named
[*Copying.txt*](https://github.com/fairy-stockfish/Fairy-Stockfish/blob/master/Copying.txt).
