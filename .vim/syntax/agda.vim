" File: ~/.vim/syntax/agda.vim

" This is reproduced from 
" http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.VIMEditing
" for convenience

if version < 600
    syn clear
elseif exists("b:current_syntax")
    finish
endif

" To tokenize, the best pattern I've found so far is this:
"   (^|\s|[.(){};])@<=token($|\s|[.(){};])@=
" The patterns @<= and @= look behind and ahead, respectively, without matching.

" `agda --vim` extends these groups:
"   agdaConstructor
"   agdaFunction
"   agdaInfixConstructor
"   agdaInfixFunction

syn match   agdaKeywords     "\v(^|\s|[.(){};])@<=(abstract|data|hiding|import|as|infix|infixl|infixr|module|mutual|open|primitive|private|public|record|renaming|rewrite|using|where|with|field|constructor|instance|syntax|pattern|inductive|coinductive)($|\s|[.(){};])@="
syn match   agdaDubious      "\v(^|\s|[.(){};])@<=(postulate|codata)($|\s|[.(){};])@="
syn match   agdaOperator     "\v(^|\s|[.(){};])@<=(let|in|forall|λ|→|-\>|:|∀|\=|\||\\)($|\s|[.(){};])@="
syn match   agdaFunction     "\v(^|\s|[.(){};])@<=(Set[0-9₀-₉]*)($|\s|[.(){};])@="
syn match   agdaNumber       "\v(^|\s|[.(){};])@<=-?[0-9]+($|\s|[.(){};])@="
syn match   agdaCharCode     contained "\\\([0-9]\+\|o[0-7]\+\|x[0-9a-fA-F]\+\|[\"\\'&\\abfnrtv]\|^[A-Z^_\[\\\]]\)"
syn match   agdaCharCode     contained "\v\\(NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|SO|SI|DLE|DC1|DC2|DC3|DC4|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|SP|DEL)"
syn match   agdaCharCodeErr  contained "\\&\|'''\+"
syn region  agdaString       start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=agdaCharCode
syn match   agdaHole         "\v(^|\s|[.(){};])@<=(\?)($|\s|[.(){};])@="
syn region  agdaX            matchgroup=agdaHole start="{!" end="!}" contains=ALL
syn match   agdaLineComment  "\v(^|\s|[.(){};])@<=--.*$" contains=@agdaInComment
syn region  agdaBlockComment start="{-"  end="-}" contains=agdaBlockComment,@agdaInComment
syn region  agdaPragma       start="{-#" end="#-}"
syn cluster agdaInComment    contains=agdaTODO,agdaFIXME,agdaXXX
syn keyword agdaTODO         contained TODO
syn keyword agdaFIXME        contained FIXME
syn keyword agdaXXX          contained XXX

hi def link agdaNumber           Number
hi def link agdaString           String
hi def link agdaConstructor      Constant
hi def link agdaCharCode         SpecialChar
hi def link agdaCharCodeErr      Error
hi def link agdaHole             WarningMsg
hi def link agdaDubious          WarningMsg
hi def link agdaKeywords         Structure
hi def link agdaFunction         Macro
hi def link agdaOperator         Operator
hi def link agdaInfixConstructor Operator
hi def link agdaInfixFunction    Operator
hi def link agdaLineComment      Comment
hi def link agdaBlockComment     Comment
hi def link agdaPragma           Comment
hi def      agdaTODO             cterm=bold,underline ctermfg=2 " green
hi def      agdaFIXME            cterm=bold,underline ctermfg=3 " yellow
hi def      agdaXXX              cterm=bold,underline ctermfg=1 " red


imap ` maF x`aa

abbreviate alpha α
abbreviate beta β
abbreviate gamma γ
abbreviate delta δ
abbreviate epsilon ε
abbreviate zeta ζ
abbreviate eta η
abbreviate thete θ
abbreviate iota ι
abbreviate kappa κ
abbreviate lambda λ
abbreviate s\\ ƛ
abbreviate mu μ
abbreviate nu ν
abbreviate xi ξ
"abbreviate omnicron ο
abbreviate pi π
abbreviate rho ρ
abbreviate sigma σ
abbreviate tau τ
abbreviate upsion υ
abbreviate phi φ
abbreviate chi χ
abbreviate psi ψ
abbreviate omega ω

"abbreviate Alpha Α
"abbreviate Beta Β
abbreviate Gamma Γ
abbreviate Delta Δ
"abbreviate Epsilon Ε
"abbreviate Zeta Ζ
"abbreviate Eta Η
abbreviate Thete Θ
"abbreviate Iota Ι
"abbreviate Kappa Κ
abbreviate Lambda Λ
"abbreviate Mu Μ
"abbreviate Nu Ν
abbreviate Xi Ξ
"abbreviate Omnicron Ο
abbreviate Pi Π
"abbreviate Rho Ρ
abbreviate Sigma Σ
"abbreviate Tau Τ
"abbreviate Upsion Υ
abbreviate Phi Φ
"abbreviate Chi Χ
abbreviate Psi Ψ
abbreviate Omega Ω

abbreviate /0 ₀
abbreviate /1 ₁
abbreviate /2 ₂
abbreviate /3 ₃
abbreviate /4 ₄
abbreviate /5 ₅
abbreviate /6 ₆
abbreviate /7 ₇
abbreviate /8 ₈
abbreviate /9 ₉
abbreviate /+ ₊
abbreviate /- ₋
abbreviate /( ₍
abbreviate /) ₎

abbreviate ^0 ⁰
abbreviate ^1 ¹
abbreviate ^2 ²
abbreviate ^3 ³
abbreviate ^4 ⁴
abbreviate ^5 ⁵
abbreviate ^6 ⁶
abbreviate ^7 ⁷
abbreviate ^8 ⁸
abbreviate ^9 ⁹
abbreviate ^n ⁿ 
abbreviate ^+ ⁺
abbreviate ^- ⁻
abbreviate ^( ⁽
abbreviate ^) ⁾
abbreviate ^a ᵃ
abbreviate ^b ᵇ
abbreviate ^c ᶜ
abbreviate ^d ᵈ
abbreviate ^e ᵉ
abbreviate ^f ᶠ
abbreviate ^g ᵍ
abbreviate ^h ʰ
abbreviate ^i ⁱ
abbreviate ^j ʲ
abbreviate ^k ᵏ
abbreviate ^l ˡ
abbreviate ^m ᵐ
abbreviate ^n ⁿ
abbreviate ^o ᵒ
abbreviate ^p ᵖ
abbreviate ^r ʳ
abbreviate ^s ˢ
abbreviate ^t ᵗ
abbreviate ^u ᵘ
abbreviate ^v ᵛ
abbreviate ^w ʷ
abbreviate ^x ˣ
abbreviate ^y ʸ
abbreviate ^z ᶻ

abbreviate -> →
abbreviate <- ←
abbreviate u-> ↑
abbreviate d-> ↓
abbreviate <>- ↔
abbreviate ud- ↕
abbreviate 0-> ⟶
abbreviate 1-> ➝
abbreviate 2-> ➔
abbreviate 3-> ➜
abbreviate 4-> ➞
abbreviate 5-> ➡
abbreviate 6-> ➾
abbreviate 7-> ➩

abbreviate => ⇒
abbreviate <= ⇐
abbreviate u=> ⇑
abbreviate d=> ⇓
abbreviate <>= ⇔
abbreviate ud= ⇕

abbreviate .> ⇢
abbreviate <. ⇠
abbreviate u.> ⇡
abbreviate d.> ⇣

abbreviate b> ⇥
abbreviate b< ⇤

abbreviate B=> ⇨
abbreviate B<= ⇦
abbreviate U=> ⇧
abbreviate D=> ⇩
abbreviate UD ⇳

abbreviate _> ⇾
abbreviate <_ ⇽
abbreviate <_> ⇿

abbreviate ~> ↝
abbreviate <~ ↜
abbreviate ~~> ⇝
abbreviate <~~ ⇜
abbreviate <~> ↭
abbreviate cont ↯

abbreviate >-> ↣
abbreviate <-< ↢
abbreviate b- ↦
abbreviate -b ↤
abbreviate bu ↥
abbreviate bd ↧
abbreviate b= ⤇
abbreviate =b ⤆

abbreviate u> ⇀
abbreviate d> ⇁
abbreviate <u ↼
abbreviate <d ↽
abbreviate ul ↿
abbreviate ur ↾
abbreviate dl ⇃
abbreviate dr ⇂

abbreviate >-< ⇄
abbreviate >=< ⇋
abbreviate 2> ⇉

abbreviate \|> ▸
abbreviate \|_> ▹
abbreviate u\|> ▴
abbreviate u\|_> ▵
abbreviate d\|> ▾
abbreviate d\|_> ▿
abbreviate \|\|> ▶
abbreviate \|\|_> ▷
abbreviate u\|\|> ▲
abbreviate u\|\|_> △
abbreviate d\|\|> ▼
abbreviate d\|\|_> ▽
abbreviate <\| ◃

abbreviate /:: ∷
abbreviate /: ∶
abbreviate /; ;
abbreviate r; ⁏
abbreviate /\| ∣
abbreviate /? ﹖
abbreviate /== ≡
abbreviate // ∥
abbreviate :: ∷
abbreviate == ≡
abbreviate \|\| ∥

abbreviate \\ λ
abbreviate forall ∀
abbreviate exists ∃
abbreviate Nat ℕ
"abbreviate Int ℤ
abbreviate inf ∞
abbreviate elem ∈
abbreviate has ∋
abbreviate times ×
abbreviate cdot ⋅
abbreviate Cdot ·
abbreviate top ⊤
abbreviate bot ⊥
abbreviate entails ⊦
abbreviate entail ⊦
abbreviate \|- ⊢
abbreviate -\| ⊣
abbreviate \|\|- ⊩
abbreviate comp ∘
abbreviate circ ∙
abbreviate dot ⋅
abbreviate mdots ⋯

abbreviate B0 𝟘
abbreviate B1 𝟙
abbreviate B2 𝟚
abbreviate B3 𝟛
abbreviate B4 𝟜
abbreviate B5 𝟝
abbreviate B6 𝟞
abbreviate B7 𝟟
abbreviate B8 𝟠
abbreviate B9 𝟡
abbreviate BA 𝔸
abbreviate BB 𝔹
abbreviate BC ℂ
abbreviate BD 𝔻
abbreviate BE 𝔼
abbreviate BF 𝔽
abbreviate BG 𝔾
abbreviate BH ℍ
abbreviate BI 𝕀
abbreviate BJ 𝕁
abbreviate BK 𝕂
abbreviate BL 𝕃
abbreviate BM 𝕄
abbreviate BN ℕ
abbreviate BO 𝕆
abbreviate BP ℙ
abbreviate BQ ℚ
abbreviate BR ℝ
abbreviate BS 𝕊
abbreviate BT 𝕋
abbreviate BU 𝕌
abbreviate BV 𝕍
abbreviate BW 𝕎
abbreviate BX 𝕏
abbreviate BY 𝕐
abbreviate BZ ℤ
abbreviate Ba 𝕒
abbreviate Bb 𝕓
abbreviate Bc 𝕔
abbreviate Bd 𝕕
abbreviate Be 𝕖
abbreviate Bf 𝕗
abbreviate Bg 𝕘
abbreviate Bh 𝕙
abbreviate Bi 𝕚
abbreviate Bj 𝕛
abbreviate Bk 𝕜
abbreviate Bl 𝕝
abbreviate Bm 𝕞
abbreviate Bn 𝕟
abbreviate Bo 𝕠
abbreviate Bp 𝕡
abbreviate Bq 𝕢
abbreviate Br 𝕣
abbreviate Bs 𝕤
abbreviate Bt 𝕥
abbreviate Bu 𝕦
abbreviate Bv 𝕧
abbreviate Bw 𝕨
abbreviate Bx 𝕩
abbreviate By 𝕪
abbreviate Bz 𝕫
abbreviate BGamma ℾ
abbreviate Bgamma ℽ
abbreviate BPi ℿ
abbreviate Bpi ℼ
abbreviate BSigma ⅀

abbreviate c+ ⊕
abbreviate c* ⊗
abbreviate c- ⊖
abbreviate c/ ⊘
abbreviate c, ⊙
abbreviate u+ ⊎
abbreviate u* ⊍
abbreviate u. ∴
abbreviate d. ∵

abbreviate empty ∅
abbreviate subset ⊂
abbreviate subseq ⊆
abbreviate supset ⊃
abbreviate supseq ⊇
abbreviate but ∖

abbreviate or ∨
abbreviate and ∧
abbreviate Or ⋁
abbreviate And ⋀
abbreviate cup ⊔
abbreviate cap ⊓
abbreviate union ∪
abbreviate inter ∩
abbreviate Union ⋃
abbreviate Anter ⋂

abbreviate sqrt √
abbreviate not ¬
abbreviate may ◇
abbreviate must □
abbreviate box □
abbreviate could ○

abbreviate c[ ⌈
abbreviate c] ⌉
abbreviate f[ ⌊
abbreviate f] ⌋
abbreviate [[ ⟦
abbreviate ]] ⟧
abbreviate /C ∁
abbreviate /< ⟨
abbreviate /> ⟩
abbreviate << ⟪
abbreviate >> ⟫
abbreviate leq ≤
abbreviate geq ≥

abbreviate endo ↻
abbreviate ando ↺
abbreviate enda ⟳
abbreviate anda ⟲

abbreviate sharp ♯
abbreviate flat ♭
abbreviate /& ⅋
abbreviate -o ⊸

abbreviate ' ′
abbreviate /, ﹐
abbreviate ok ✓
abbreviate /... …
abbreviate /* ⁎
abbreviate star ★
abbreviate approx ≈
abbreviate /~ ∼
abbreviate 2~ ≈
abbreviate =/= ≢
abbreviate =~= ≅
abbreviate =?= ≟
abbreviate qed ∎
abbreviate := ≔

abbreviate .^ ⋅̂
abbreviate c^ ∘̂

abbreviate /l ℓ
abbreviate en- –
