define(`rename_t', `∀ {Γ₁ Γ₂} → (Γ₁ → Γ₂) → $1 Γ₁ → $1 Γ₂')
define(`rename_v', `var ($2 $3)')
define(`rename_w', `(rename (weaken-map $2) $3)')

define(`weaken_t', `∀ {Γ A} → $1 Γ → $1 (Γ ⊎ A)')
define(`weaken_v', `var (inj₁ $2)')
define(`weaken_w', `(rename swap-last (weaken $2))')

define(`substitute_t', `∀ {Γ₁ Γ₂} → (Γ₁ → $1 Γ₂) → $1 Γ₁ → $1 Γ₂')
define(`substitute_v', `$2 $3')
define(`substitute_w', `(substitute (weaken-sub′ $1 var weaken $2) $3)')
