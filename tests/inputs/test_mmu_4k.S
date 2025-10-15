
/*
 * This file was automatically generated using arm64-pgtable-tool.
 * See: https://github.com/ashwio/arm64-pgtable-tool
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * This code programs the following translation table structure:
 *
 *         level 1 table @ 0x40400000
 *         [#   0]---------------------------\
 *                 level 2 table @ 0x40401000
 *                 [# 108]---------------------------\
 *                         level 3 table @ 0x40402000
 *                         [#   0] 0x00000d800000-0x00000d800fff, Device, TUBE
 *                         [#   1] 0x00000d801000-0x00000d801fff, Device, TUBE
 *                 [# 224]---------------------------\
 *                         level 3 table @ 0x40403000
 *                         [# 144] 0x00001c090000-0x00001c090fff, Device, UART0
 *                 [# 352]---------------------------\
 *                         level 3 table @ 0x40404000
 *                         [#   0] 0x00002c000000-0x00002c000fff, Device, GICC
 *                         [#   1] 0x00002c001000-0x00002c001fff, Device, GICC
 *                 [# 368]---------------------------\
 *                         level 3 table @ 0x40405000
 *                         [#   0] 0x00002e000000-0x00002e000fff, Code, CODE
 *                         [#   1] 0x00002e001000-0x00002e001fff, Code, CODE
 *                         [#   2] 0x00002e002000-0x00002e002fff, Code, CODE
 *                         [#   3] 0x00002e003000-0x00002e003fff, Code, CODE
 *                         [#   4] 0x00002e004000-0x00002e004fff, Code, CODE
 *                         [#   5] 0x00002e005000-0x00002e005fff, Code, CODE
 *                         [#   6] 0x00002e006000-0x00002e006fff, Code, CODE
 *                         [#   7] 0x00002e007000-0x00002e007fff, Code, CODE
 *                         [#   8] 0x00002e008000-0x00002e008fff, Code, CODE
 *                         [#   9] 0x00002e009000-0x00002e009fff, Code, CODE
 *                         [#  10] 0x00002e00a000-0x00002e00afff, Code, CODE
 *                         [#  11] 0x00002e00b000-0x00002e00bfff, Code, CODE
 *                         [#  12] 0x00002e00c000-0x00002e00cfff, Code, CODE
 *                         [#  13] 0x00002e00d000-0x00002e00dfff, Code, CODE
 *                         [#  14] 0x00002e00e000-0x00002e00efff, Code, CODE
 *                         [#  15] 0x00002e00f000-0x00002e00ffff, Code, CODE
 *                 [# 376]---------------------------\
 *                         level 3 table @ 0x40406000
 *                         [#   0] 0x00002f000000-0x00002f000fff, Device, GICv3 GICD
 *                         [#   1] 0x00002f001000-0x00002f001fff, Device, GICv3 GICD
 *                         [#   2] 0x00002f002000-0x00002f002fff, Device, GICv3 GICD
 *                         [#   3] 0x00002f003000-0x00002f003fff, Device, GICv3 GICD
 *                         [#   4] 0x00002f004000-0x00002f004fff, Device, GICv3 GICD
 *                         [#   5] 0x00002f005000-0x00002f005fff, Device, GICv3 GICD
 *                         [#   6] 0x00002f006000-0x00002f006fff, Device, GICv3 GICD
 *                         [#   7] 0x00002f007000-0x00002f007fff, Device, GICv3 GICD
 *                         [#   8] 0x00002f008000-0x00002f008fff, Device, GICv3 GICD
 *                         [#   9] 0x00002f009000-0x00002f009fff, Device, GICv3 GICD
 *                         [#  10] 0x00002f00a000-0x00002f00afff, Device, GICv3 GICD
 *                         [#  11] 0x00002f00b000-0x00002f00bfff, Device, GICv3 GICD
 *                         [#  12] 0x00002f00c000-0x00002f00cfff, Device, GICv3 GICD
 *                         [#  13] 0x00002f00d000-0x00002f00dfff, Device, GICv3 GICD
 *                         [#  14] 0x00002f00e000-0x00002f00efff, Device, GICv3 GICD
 *                         [#  15] 0x00002f00f000-0x00002f00ffff, Device, GICv3 GICD
 *                         [# 256] 0x00002f100000-0x00002f100fff, Device, GICv3 GICR
 *                         [# 257] 0x00002f101000-0x00002f101fff, Device, GICv3 GICR
 *                         [# 258] 0x00002f102000-0x00002f102fff, Device, GICv3 GICR
 *                         [# 259] 0x00002f103000-0x00002f103fff, Device, GICv3 GICR
 *                         [# 260] 0x00002f104000-0x00002f104fff, Device, GICv3 GICR
 *                         [# 261] 0x00002f105000-0x00002f105fff, Device, GICv3 GICR
 *                         [# 262] 0x00002f106000-0x00002f106fff, Device, GICv3 GICR
 *                         [# 263] 0x00002f107000-0x00002f107fff, Device, GICv3 GICR
 *                         [# 264] 0x00002f108000-0x00002f108fff, Device, GICv3 GICR
 *                         [# 265] 0x00002f109000-0x00002f109fff, Device, GICv3 GICR
 *                         [# 266] 0x00002f10a000-0x00002f10afff, Device, GICv3 GICR
 *                         [# 267] 0x00002f10b000-0x00002f10bfff, Device, GICv3 GICR
 *                         [# 268] 0x00002f10c000-0x00002f10cfff, Device, GICv3 GICR
 *                         [# 269] 0x00002f10d000-0x00002f10dfff, Device, GICv3 GICR
 *                         [# 270] 0x00002f10e000-0x00002f10efff, Device, GICv3 GICR
 *                         [# 271] 0x00002f10f000-0x00002f10ffff, Device, GICv3 GICR
 *                         [# 272] 0x00002f110000-0x00002f110fff, Device, GICv3 GICR
 *                         [# 273] 0x00002f111000-0x00002f111fff, Device, GICv3 GICR
 *                         [# 274] 0x00002f112000-0x00002f112fff, Device, GICv3 GICR
 *                         [# 275] 0x00002f113000-0x00002f113fff, Device, GICv3 GICR
 *                         [# 276] 0x00002f114000-0x00002f114fff, Device, GICv3 GICR
 *                         [# 277] 0x00002f115000-0x00002f115fff, Device, GICv3 GICR
 *                         [# 278] 0x00002f116000-0x00002f116fff, Device, GICv3 GICR
 *                         [# 279] 0x00002f117000-0x00002f117fff, Device, GICv3 GICR
 *                         [# 280] 0x00002f118000-0x00002f118fff, Device, GICv3 GICR
 *                         [# 281] 0x00002f119000-0x00002f119fff, Device, GICv3 GICR
 *                         [# 282] 0x00002f11a000-0x00002f11afff, Device, GICv3 GICR
 *                         [# 283] 0x00002f11b000-0x00002f11bfff, Device, GICv3 GICR
 *                         [# 284] 0x00002f11c000-0x00002f11cfff, Device, GICv3 GICR
 *                         [# 285] 0x00002f11d000-0x00002f11dfff, Device, GICv3 GICR
 *                         [# 286] 0x00002f11e000-0x00002f11efff, Device, GICv3 GICR
 *                         [# 287] 0x00002f11f000-0x00002f11ffff, Device, GICv3 GICR
 *                         [# 288] 0x00002f120000-0x00002f120fff, Device, GICv3 GICR
 *                         [# 289] 0x00002f121000-0x00002f121fff, Device, GICv3 GICR
 *                         [# 290] 0x00002f122000-0x00002f122fff, Device, GICv3 GICR
 *                         [# 291] 0x00002f123000-0x00002f123fff, Device, GICv3 GICR
 *                         [# 292] 0x00002f124000-0x00002f124fff, Device, GICv3 GICR
 *                         [# 293] 0x00002f125000-0x00002f125fff, Device, GICv3 GICR
 *                         [# 294] 0x00002f126000-0x00002f126fff, Device, GICv3 GICR
 *                         [# 295] 0x00002f127000-0x00002f127fff, Device, GICv3 GICR
 *                         [# 296] 0x00002f128000-0x00002f128fff, Device, GICv3 GICR
 *                         [# 297] 0x00002f129000-0x00002f129fff, Device, GICv3 GICR
 *                         [# 298] 0x00002f12a000-0x00002f12afff, Device, GICv3 GICR
 *                         [# 299] 0x00002f12b000-0x00002f12bfff, Device, GICv3 GICR
 *                         [# 300] 0x00002f12c000-0x00002f12cfff, Device, GICv3 GICR
 *                         [# 301] 0x00002f12d000-0x00002f12dfff, Device, GICv3 GICR
 *                         [# 302] 0x00002f12e000-0x00002f12efff, Device, GICv3 GICR
 *                         [# 303] 0x00002f12f000-0x00002f12ffff, Device, GICv3 GICR
 *                         [# 304] 0x00002f130000-0x00002f130fff, Device, GICv3 GICR
 *                         [# 305] 0x00002f131000-0x00002f131fff, Device, GICv3 GICR
 *                         [# 306] 0x00002f132000-0x00002f132fff, Device, GICv3 GICR
 *                         [# 307] 0x00002f133000-0x00002f133fff, Device, GICv3 GICR
 *                         [# 308] 0x00002f134000-0x00002f134fff, Device, GICv3 GICR
 *                         [# 309] 0x00002f135000-0x00002f135fff, Device, GICv3 GICR
 *                         [# 310] 0x00002f136000-0x00002f136fff, Device, GICv3 GICR
 *                         [# 311] 0x00002f137000-0x00002f137fff, Device, GICv3 GICR
 *                         [# 312] 0x00002f138000-0x00002f138fff, Device, GICv3 GICR
 *                         [# 313] 0x00002f139000-0x00002f139fff, Device, GICv3 GICR
 *                         [# 314] 0x00002f13a000-0x00002f13afff, Device, GICv3 GICR
 *                         [# 315] 0x00002f13b000-0x00002f13bfff, Device, GICv3 GICR
 *                         [# 316] 0x00002f13c000-0x00002f13cfff, Device, GICv3 GICR
 *                         [# 317] 0x00002f13d000-0x00002f13dfff, Device, GICv3 GICR
 *                         [# 318] 0x00002f13e000-0x00002f13efff, Device, GICv3 GICR
 *                         [# 319] 0x00002f13f000-0x00002f13ffff, Device, GICv3 GICR
 *                         [# 320] 0x00002f140000-0x00002f140fff, Device, GICv3 GICR
 *                         [# 321] 0x00002f141000-0x00002f141fff, Device, GICv3 GICR
 *                         [# 322] 0x00002f142000-0x00002f142fff, Device, GICv3 GICR
 *                         [# 323] 0x00002f143000-0x00002f143fff, Device, GICv3 GICR
 *                         [# 324] 0x00002f144000-0x00002f144fff, Device, GICv3 GICR
 *                         [# 325] 0x00002f145000-0x00002f145fff, Device, GICv3 GICR
 *                         [# 326] 0x00002f146000-0x00002f146fff, Device, GICv3 GICR
 *                         [# 327] 0x00002f147000-0x00002f147fff, Device, GICv3 GICR
 *                         [# 328] 0x00002f148000-0x00002f148fff, Device, GICv3 GICR
 *                         [# 329] 0x00002f149000-0x00002f149fff, Device, GICv3 GICR
 *                         [# 330] 0x00002f14a000-0x00002f14afff, Device, GICv3 GICR
 *                         [# 331] 0x00002f14b000-0x00002f14bfff, Device, GICv3 GICR
 *                         [# 332] 0x00002f14c000-0x00002f14cfff, Device, GICv3 GICR
 *                         [# 333] 0x00002f14d000-0x00002f14dfff, Device, GICv3 GICR
 *                         [# 334] 0x00002f14e000-0x00002f14efff, Device, GICv3 GICR
 *                         [# 335] 0x00002f14f000-0x00002f14ffff, Device, GICv3 GICR
 *                         [# 336] 0x00002f150000-0x00002f150fff, Device, GICv3 GICR
 *                         [# 337] 0x00002f151000-0x00002f151fff, Device, GICv3 GICR
 *                         [# 338] 0x00002f152000-0x00002f152fff, Device, GICv3 GICR
 *                         [# 339] 0x00002f153000-0x00002f153fff, Device, GICv3 GICR
 *                         [# 340] 0x00002f154000-0x00002f154fff, Device, GICv3 GICR
 *                         [# 341] 0x00002f155000-0x00002f155fff, Device, GICv3 GICR
 *                         [# 342] 0x00002f156000-0x00002f156fff, Device, GICv3 GICR
 *                         [# 343] 0x00002f157000-0x00002f157fff, Device, GICv3 GICR
 *                         [# 344] 0x00002f158000-0x00002f158fff, Device, GICv3 GICR
 *                         [# 345] 0x00002f159000-0x00002f159fff, Device, GICv3 GICR
 *                         [# 346] 0x00002f15a000-0x00002f15afff, Device, GICv3 GICR
 *                         [# 347] 0x00002f15b000-0x00002f15bfff, Device, GICv3 GICR
 *                         [# 348] 0x00002f15c000-0x00002f15cfff, Device, GICv3 GICR
 *                         [# 349] 0x00002f15d000-0x00002f15dfff, Device, GICv3 GICR
 *                         [# 350] 0x00002f15e000-0x00002f15efff, Device, GICv3 GICR
 *                         [# 351] 0x00002f15f000-0x00002f15ffff, Device, GICv3 GICR
 *                         [# 352] 0x00002f160000-0x00002f160fff, Device, GICv3 GICR
 *                         [# 353] 0x00002f161000-0x00002f161fff, Device, GICv3 GICR
 *                         [# 354] 0x00002f162000-0x00002f162fff, Device, GICv3 GICR
 *                         [# 355] 0x00002f163000-0x00002f163fff, Device, GICv3 GICR
 *                         [# 356] 0x00002f164000-0x00002f164fff, Device, GICv3 GICR
 *                         [# 357] 0x00002f165000-0x00002f165fff, Device, GICv3 GICR
 *                         [# 358] 0x00002f166000-0x00002f166fff, Device, GICv3 GICR
 *                         [# 359] 0x00002f167000-0x00002f167fff, Device, GICv3 GICR
 *                         [# 360] 0x00002f168000-0x00002f168fff, Device, GICv3 GICR
 *                         [# 361] 0x00002f169000-0x00002f169fff, Device, GICv3 GICR
 *                         [# 362] 0x00002f16a000-0x00002f16afff, Device, GICv3 GICR
 *                         [# 363] 0x00002f16b000-0x00002f16bfff, Device, GICv3 GICR
 *                         [# 364] 0x00002f16c000-0x00002f16cfff, Device, GICv3 GICR
 *                         [# 365] 0x00002f16d000-0x00002f16dfff, Device, GICv3 GICR
 *                         [# 366] 0x00002f16e000-0x00002f16efff, Device, GICv3 GICR
 *                         [# 367] 0x00002f16f000-0x00002f16ffff, Device, GICv3 GICR
 *                         [# 368] 0x00002f170000-0x00002f170fff, Device, GICv3 GICR
 *                         [# 369] 0x00002f171000-0x00002f171fff, Device, GICv3 GICR
 *                         [# 370] 0x00002f172000-0x00002f172fff, Device, GICv3 GICR
 *                         [# 371] 0x00002f173000-0x00002f173fff, Device, GICv3 GICR
 *                         [# 372] 0x00002f174000-0x00002f174fff, Device, GICv3 GICR
 *                         [# 373] 0x00002f175000-0x00002f175fff, Device, GICv3 GICR
 *                         [# 374] 0x00002f176000-0x00002f176fff, Device, GICv3 GICR
 *                         [# 375] 0x00002f177000-0x00002f177fff, Device, GICv3 GICR
 *                         [# 376] 0x00002f178000-0x00002f178fff, Device, GICv3 GICR
 *                         [# 377] 0x00002f179000-0x00002f179fff, Device, GICv3 GICR
 *                         [# 378] 0x00002f17a000-0x00002f17afff, Device, GICv3 GICR
 *                         [# 379] 0x00002f17b000-0x00002f17bfff, Device, GICv3 GICR
 *                         [# 380] 0x00002f17c000-0x00002f17cfff, Device, GICv3 GICR
 *                         [# 381] 0x00002f17d000-0x00002f17dfff, Device, GICv3 GICR
 *                         [# 382] 0x00002f17e000-0x00002f17efff, Device, GICv3 GICR
 *                         [# 383] 0x00002f17f000-0x00002f17ffff, Device, GICv3 GICR
 *                         [# 384] 0x00002f180000-0x00002f180fff, Device, GICv3 GICR
 *                         [# 385] 0x00002f181000-0x00002f181fff, Device, GICv3 GICR
 *                         [# 386] 0x00002f182000-0x00002f182fff, Device, GICv3 GICR
 *                         [# 387] 0x00002f183000-0x00002f183fff, Device, GICv3 GICR
 *                         [# 388] 0x00002f184000-0x00002f184fff, Device, GICv3 GICR
 *                         [# 389] 0x00002f185000-0x00002f185fff, Device, GICv3 GICR
 *                         [# 390] 0x00002f186000-0x00002f186fff, Device, GICv3 GICR
 *                         [# 391] 0x00002f187000-0x00002f187fff, Device, GICv3 GICR
 *                         [# 392] 0x00002f188000-0x00002f188fff, Device, GICv3 GICR
 *                         [# 393] 0x00002f189000-0x00002f189fff, Device, GICv3 GICR
 *                         [# 394] 0x00002f18a000-0x00002f18afff, Device, GICv3 GICR
 *                         [# 395] 0x00002f18b000-0x00002f18bfff, Device, GICv3 GICR
 *                         [# 396] 0x00002f18c000-0x00002f18cfff, Device, GICv3 GICR
 *                         [# 397] 0x00002f18d000-0x00002f18dfff, Device, GICv3 GICR
 *                         [# 398] 0x00002f18e000-0x00002f18efff, Device, GICv3 GICR
 *                         [# 399] 0x00002f18f000-0x00002f18ffff, Device, GICv3 GICR
 *                         [# 400] 0x00002f190000-0x00002f190fff, Device, GICv3 GICR
 *                         [# 401] 0x00002f191000-0x00002f191fff, Device, GICv3 GICR
 *                         [# 402] 0x00002f192000-0x00002f192fff, Device, GICv3 GICR
 *                         [# 403] 0x00002f193000-0x00002f193fff, Device, GICv3 GICR
 *                         [# 404] 0x00002f194000-0x00002f194fff, Device, GICv3 GICR
 *                         [# 405] 0x00002f195000-0x00002f195fff, Device, GICv3 GICR
 *                         [# 406] 0x00002f196000-0x00002f196fff, Device, GICv3 GICR
 *                         [# 407] 0x00002f197000-0x00002f197fff, Device, GICv3 GICR
 *                         [# 408] 0x00002f198000-0x00002f198fff, Device, GICv3 GICR
 *                         [# 409] 0x00002f199000-0x00002f199fff, Device, GICv3 GICR
 *                         [# 410] 0x00002f19a000-0x00002f19afff, Device, GICv3 GICR
 *                         [# 411] 0x00002f19b000-0x00002f19bfff, Device, GICv3 GICR
 *                         [# 412] 0x00002f19c000-0x00002f19cfff, Device, GICv3 GICR
 *                         [# 413] 0x00002f19d000-0x00002f19dfff, Device, GICv3 GICR
 *                         [# 414] 0x00002f19e000-0x00002f19efff, Device, GICv3 GICR
 *                         [# 415] 0x00002f19f000-0x00002f19ffff, Device, GICv3 GICR
 *                         [# 416] 0x00002f1a0000-0x00002f1a0fff, Device, GICv3 GICR
 *                         [# 417] 0x00002f1a1000-0x00002f1a1fff, Device, GICv3 GICR
 *                         [# 418] 0x00002f1a2000-0x00002f1a2fff, Device, GICv3 GICR
 *                         [# 419] 0x00002f1a3000-0x00002f1a3fff, Device, GICv3 GICR
 *                         [# 420] 0x00002f1a4000-0x00002f1a4fff, Device, GICv3 GICR
 *                         [# 421] 0x00002f1a5000-0x00002f1a5fff, Device, GICv3 GICR
 *                         [# 422] 0x00002f1a6000-0x00002f1a6fff, Device, GICv3 GICR
 *                         [# 423] 0x00002f1a7000-0x00002f1a7fff, Device, GICv3 GICR
 *                         [# 424] 0x00002f1a8000-0x00002f1a8fff, Device, GICv3 GICR
 *                         [# 425] 0x00002f1a9000-0x00002f1a9fff, Device, GICv3 GICR
 *                         [# 426] 0x00002f1aa000-0x00002f1aafff, Device, GICv3 GICR
 *                         [# 427] 0x00002f1ab000-0x00002f1abfff, Device, GICv3 GICR
 *                         [# 428] 0x00002f1ac000-0x00002f1acfff, Device, GICv3 GICR
 *                         [# 429] 0x00002f1ad000-0x00002f1adfff, Device, GICv3 GICR
 *                         [# 430] 0x00002f1ae000-0x00002f1aefff, Device, GICv3 GICR
 *                         [# 431] 0x00002f1af000-0x00002f1affff, Device, GICv3 GICR
 *                         [# 432] 0x00002f1b0000-0x00002f1b0fff, Device, GICv3 GICR
 *                         [# 433] 0x00002f1b1000-0x00002f1b1fff, Device, GICv3 GICR
 *                         [# 434] 0x00002f1b2000-0x00002f1b2fff, Device, GICv3 GICR
 *                         [# 435] 0x00002f1b3000-0x00002f1b3fff, Device, GICv3 GICR
 *                         [# 436] 0x00002f1b4000-0x00002f1b4fff, Device, GICv3 GICR
 *                         [# 437] 0x00002f1b5000-0x00002f1b5fff, Device, GICv3 GICR
 *                         [# 438] 0x00002f1b6000-0x00002f1b6fff, Device, GICv3 GICR
 *                         [# 439] 0x00002f1b7000-0x00002f1b7fff, Device, GICv3 GICR
 *                         [# 440] 0x00002f1b8000-0x00002f1b8fff, Device, GICv3 GICR
 *                         [# 441] 0x00002f1b9000-0x00002f1b9fff, Device, GICv3 GICR
 *                         [# 442] 0x00002f1ba000-0x00002f1bafff, Device, GICv3 GICR
 *                         [# 443] 0x00002f1bb000-0x00002f1bbfff, Device, GICv3 GICR
 *                         [# 444] 0x00002f1bc000-0x00002f1bcfff, Device, GICv3 GICR
 *                         [# 445] 0x00002f1bd000-0x00002f1bdfff, Device, GICv3 GICR
 *                         [# 446] 0x00002f1be000-0x00002f1befff, Device, GICv3 GICR
 *                         [# 447] 0x00002f1bf000-0x00002f1bffff, Device, GICv3 GICR
 *                         [# 448] 0x00002f1c0000-0x00002f1c0fff, Device, GICv3 GICR
 *                         [# 449] 0x00002f1c1000-0x00002f1c1fff, Device, GICv3 GICR
 *                         [# 450] 0x00002f1c2000-0x00002f1c2fff, Device, GICv3 GICR
 *                         [# 451] 0x00002f1c3000-0x00002f1c3fff, Device, GICv3 GICR
 *                         [# 452] 0x00002f1c4000-0x00002f1c4fff, Device, GICv3 GICR
 *                         [# 453] 0x00002f1c5000-0x00002f1c5fff, Device, GICv3 GICR
 *                         [# 454] 0x00002f1c6000-0x00002f1c6fff, Device, GICv3 GICR
 *                         [# 455] 0x00002f1c7000-0x00002f1c7fff, Device, GICv3 GICR
 *                         [# 456] 0x00002f1c8000-0x00002f1c8fff, Device, GICv3 GICR
 *                         [# 457] 0x00002f1c9000-0x00002f1c9fff, Device, GICv3 GICR
 *                         [# 458] 0x00002f1ca000-0x00002f1cafff, Device, GICv3 GICR
 *                         [# 459] 0x00002f1cb000-0x00002f1cbfff, Device, GICv3 GICR
 *                         [# 460] 0x00002f1cc000-0x00002f1ccfff, Device, GICv3 GICR
 *                         [# 461] 0x00002f1cd000-0x00002f1cdfff, Device, GICv3 GICR
 *                         [# 462] 0x00002f1ce000-0x00002f1cefff, Device, GICv3 GICR
 *                         [# 463] 0x00002f1cf000-0x00002f1cffff, Device, GICv3 GICR
 *                         [# 464] 0x00002f1d0000-0x00002f1d0fff, Device, GICv3 GICR
 *                         [# 465] 0x00002f1d1000-0x00002f1d1fff, Device, GICv3 GICR
 *                         [# 466] 0x00002f1d2000-0x00002f1d2fff, Device, GICv3 GICR
 *                         [# 467] 0x00002f1d3000-0x00002f1d3fff, Device, GICv3 GICR
 *                         [# 468] 0x00002f1d4000-0x00002f1d4fff, Device, GICv3 GICR
 *                         [# 469] 0x00002f1d5000-0x00002f1d5fff, Device, GICv3 GICR
 *                         [# 470] 0x00002f1d6000-0x00002f1d6fff, Device, GICv3 GICR
 *                         [# 471] 0x00002f1d7000-0x00002f1d7fff, Device, GICv3 GICR
 *                         [# 472] 0x00002f1d8000-0x00002f1d8fff, Device, GICv3 GICR
 *                         [# 473] 0x00002f1d9000-0x00002f1d9fff, Device, GICv3 GICR
 *                         [# 474] 0x00002f1da000-0x00002f1dafff, Device, GICv3 GICR
 *                         [# 475] 0x00002f1db000-0x00002f1dbfff, Device, GICv3 GICR
 *                         [# 476] 0x00002f1dc000-0x00002f1dcfff, Device, GICv3 GICR
 *                         [# 477] 0x00002f1dd000-0x00002f1ddfff, Device, GICv3 GICR
 *                         [# 478] 0x00002f1de000-0x00002f1defff, Device, GICv3 GICR
 *                         [# 479] 0x00002f1df000-0x00002f1dffff, Device, GICv3 GICR
 *                         [# 480] 0x00002f1e0000-0x00002f1e0fff, Device, GICv3 GICR
 *                         [# 481] 0x00002f1e1000-0x00002f1e1fff, Device, GICv3 GICR
 *                         [# 482] 0x00002f1e2000-0x00002f1e2fff, Device, GICv3 GICR
 *                         [# 483] 0x00002f1e3000-0x00002f1e3fff, Device, GICv3 GICR
 *                         [# 484] 0x00002f1e4000-0x00002f1e4fff, Device, GICv3 GICR
 *                         [# 485] 0x00002f1e5000-0x00002f1e5fff, Device, GICv3 GICR
 *                         [# 486] 0x00002f1e6000-0x00002f1e6fff, Device, GICv3 GICR
 *                         [# 487] 0x00002f1e7000-0x00002f1e7fff, Device, GICv3 GICR
 *                         [# 488] 0x00002f1e8000-0x00002f1e8fff, Device, GICv3 GICR
 *                         [# 489] 0x00002f1e9000-0x00002f1e9fff, Device, GICv3 GICR
 *                         [# 490] 0x00002f1ea000-0x00002f1eafff, Device, GICv3 GICR
 *                         [# 491] 0x00002f1eb000-0x00002f1ebfff, Device, GICv3 GICR
 *                         [# 492] 0x00002f1ec000-0x00002f1ecfff, Device, GICv3 GICR
 *                         [# 493] 0x00002f1ed000-0x00002f1edfff, Device, GICv3 GICR
 *                         [# 494] 0x00002f1ee000-0x00002f1eefff, Device, GICv3 GICR
 *                         [# 495] 0x00002f1ef000-0x00002f1effff, Device, GICv3 GICR
 *                         [# 496] 0x00002f1f0000-0x00002f1f0fff, Device, GICv3 GICR
 *                         [# 497] 0x00002f1f1000-0x00002f1f1fff, Device, GICv3 GICR
 *                         [# 498] 0x00002f1f2000-0x00002f1f2fff, Device, GICv3 GICR
 *                         [# 499] 0x00002f1f3000-0x00002f1f3fff, Device, GICv3 GICR
 *                         [# 500] 0x00002f1f4000-0x00002f1f4fff, Device, GICv3 GICR
 *                         [# 501] 0x00002f1f5000-0x00002f1f5fff, Device, GICv3 GICR
 *                         [# 502] 0x00002f1f6000-0x00002f1f6fff, Device, GICv3 GICR
 *                         [# 503] 0x00002f1f7000-0x00002f1f7fff, Device, GICv3 GICR
 *                         [# 504] 0x00002f1f8000-0x00002f1f8fff, Device, GICv3 GICR
 *                         [# 505] 0x00002f1f9000-0x00002f1f9fff, Device, GICv3 GICR
 *                         [# 506] 0x00002f1fa000-0x00002f1fafff, Device, GICv3 GICR
 *                         [# 507] 0x00002f1fb000-0x00002f1fbfff, Device, GICv3 GICR
 *                         [# 508] 0x00002f1fc000-0x00002f1fcfff, Device, GICv3 GICR
 *                         [# 509] 0x00002f1fd000-0x00002f1fdfff, Device, GICv3 GICR
 *                         [# 510] 0x00002f1fe000-0x00002f1fefff, Device, GICv3 GICR
 *                         [# 511] 0x00002f1ff000-0x00002f1fffff, Device, GICv3 GICR
 *         [#   2] 0x000080000000-0x0000bfffffff, RW_Data, Non-Trusted DRAM
 *         [#   3] 0x0000c0000000-0x0000ffffffff, RW_Data, Non-Trusted DRAM
 *
 * The following command line arguments were passed to arm64-pgtable-tool:
 *
 *      -i base-mmu.txt
 *      -ttb 0x40400000
 *      -el 1
 *      -tg 4K
 *      -tsz 32
 *
 * This memory map requires a total of 7 translation tables.
 * Each table occupies 4K of memory (0x1000 bytes).
 * The buffer pointed to by 0x40400000 must therefore be 7x 4K = 0x7000 bytes long.
 * It is the programmer's responsibility to guarantee this.
 *
 * The programmer must also ensure that the virtual memory region containing the
 * translation tables is itself marked as NORMAL in the memory map file.
 */
/* base-mmu.txt contents:
0xd800020,     1K, DEVICE, TUBE
0x01C090000,   4K, DEVICE, UART0
0x02C000000,   8K, DEVICE, GICC
0x02E000000,  64K, CODE,   CODE
0x02F000000,  64K, DEVICE, GICv3 GICD
0x02F100000,   1M, DEVICE, GICv3 GICR
0x080000000,   2G, RW_DATA, Non-Trusted DRAM
*/

.include "tests/inputs/helpers.S.inc"

mmu_on:

zero_out_tables:

    LDR     x2, =0x40400000              // address of first table
    LDR     x3, =0x7000                  // combined length of all tables
    LSR     x3, x3, #5                   // number of required STP instructions
    FMOV    d0, xzr                      // clear q0
1:
    STP     q0, q0, [x2], #32            // zero out 4 table entries at a time
    SUBS    x3, x3, #1
    B.NE    1b

load_descriptor_templates:

    LDR     x2, =0x20000000000705        // Device block
    LDR     x3, =0x20000000000707        // Device page
    LDR     x4, =0x20000000000701        // RW data block
    LDR     x5, =0x20000000000703        // RW data page
    LDR     x20, =0x781                  // code block
    LDR     x21, =0x783                  // code page


program_table_0:

    LDR     x8, =0x40400000              // base address of this table
    LDR     x9, =0x40000000              // chunk size

program_table_0_entry_0:

    LDR     x10, =0                      // idx
    LDR     x11, =0x40401000             // next-level table address
    ORR     x11, x11, #0x3               // next-level table descriptor
    STR     x11, [x8, x10, lsl #3]       // write entry into table

program_table_0_entry_2_to_3:

    LDR     x10, =2                      // idx
    LDR     x11, =2                      // number of contiguous entries
    LDR     x12, =0x80000000             // output address of entry[idx]
1:
    ORR     x12, x12, x4                 // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b
program_table_1:

    LDR     x8, =0x40401000              // base address of this table
    LDR     x9, =0x200000                // chunk size

program_table_1_entry_108:

    LDR     x10, =108                    // idx
    LDR     x11, =0x40402000             // next-level table address
    ORR     x11, x11, #0x3               // next-level table descriptor
    STR     x11, [x8, x10, lsl #3]       // write entry into table

program_table_1_entry_224:

    LDR     x10, =224                    // idx
    LDR     x11, =0x40403000             // next-level table address
    ORR     x11, x11, #0x3               // next-level table descriptor
    STR     x11, [x8, x10, lsl #3]       // write entry into table

program_table_1_entry_352:

    LDR     x10, =352                    // idx
    LDR     x11, =0x40404000             // next-level table address
    ORR     x11, x11, #0x3               // next-level table descriptor
    STR     x11, [x8, x10, lsl #3]       // write entry into table

program_table_1_entry_368:

    LDR     x10, =368                    // idx
    LDR     x11, =0x40405000             // next-level table address
    ORR     x11, x11, #0x3               // next-level table descriptor
    STR     x11, [x8, x10, lsl #3]       // write entry into table

program_table_1_entry_376:

    LDR     x10, =376                    // idx
    LDR     x11, =0x40406000             // next-level table address
    ORR     x11, x11, #0x3               // next-level table descriptor
    STR     x11, [x8, x10, lsl #3]       // write entry into table
program_table_2:

    LDR     x8, =0x40402000              // base address of this table
    LDR     x9, =0x1000                  // chunk size

program_table_2_entry_0_to_1:

    LDR     x10, =0                      // idx
    LDR     x11, =2                      // number of contiguous entries
    LDR     x12, =0xd800000              // output address of entry[idx]
1:
    ORR     x12, x12, x3                 // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b
program_table_3:

    LDR     x8, =0x40403000              // base address of this table
    LDR     x9, =0x1000                  // chunk size

program_table_3_entry_144:

    LDR     x10, =144                    // idx
    LDR     x11, =1                      // number of contiguous entries
    LDR     x12, =0x1c090000             // output address of entry[idx]
1:
    ORR     x12, x12, x3                 // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b
program_table_4:

    LDR     x8, =0x40404000              // base address of this table
    LDR     x9, =0x1000                  // chunk size

program_table_4_entry_0_to_1:

    LDR     x10, =0                      // idx
    LDR     x11, =2                      // number of contiguous entries
    LDR     x12, =0x2c000000             // output address of entry[idx]
1:
    ORR     x12, x12, x3                 // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b
program_table_5:

    LDR     x8, =0x40405000              // base address of this table
    LDR     x9, =0x1000                  // chunk size

program_table_5_entry_0_to_15:

    LDR     x10, =0                      // idx
    LDR     x11, =16                     // number of contiguous entries
    LDR     x12, =0x2e000000             // output address of entry[idx]
1:
    ORR     x12, x12, x21                // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b
program_table_6:

    LDR     x8, =0x40406000              // base address of this table
    LDR     x9, =0x1000                  // chunk size

program_table_6_entry_0_to_15:

    LDR     x10, =0                      // idx
    LDR     x11, =16                     // number of contiguous entries
    LDR     x12, =0x2f000000             // output address of entry[idx]
1:
    ORR     x12, x12, x3                 // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b

program_table_6_entry_256_to_511:

    LDR     x10, =256                    // idx
    LDR     x11, =256                    // number of contiguous entries
    LDR     x12, =0x2f100000             // output address of entry[idx]
1:
    ORR     x12, x12, x3                 // merge output address with template
    STR     X12, [x8, x10, lsl #3]       // write entry into table
    ADD     x10, x10, #1                 // prepare for next entry idx+1
    ADD     x12, x12, x9                 // add chunk to address
    SUBS    x11, x11, #1                 // loop as required
    B.NE    1b

end:

    LDR     x1, =0x40400000              // program ttbr0 on this CPU
    MSR     ttbr0_el1, x1
    LDR     x1, =0xff                    // program mair on this CPU
    MSR     mair_el1, x1
    LDR     x1, =0x803520                // program tcr on this CPU
    MSR     tcr_el1, x1
    ISB
    MRS     x2, tcr_el1                  // verify CPU supports desired config
    CMP     x2, x1
    B.NE    .
    LDR     x1, =0x1005                  // program sctlr on this CPU
    MSR     sctlr_el1, x1
    ISB                                  // synchronize context on this CPU

write_to_tube w30, x29
