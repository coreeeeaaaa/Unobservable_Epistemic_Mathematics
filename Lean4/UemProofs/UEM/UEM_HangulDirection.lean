import UemProofs.UEM.UEM_Calculus

namespace UEM

/-!
Directional tagging for Jungseong (vowel) components.
This is a pure, structural mapping: no external semantics are assumed.
We use the core `Direction` type from `UEM_Calculus`.
-/

def directionOfVowel : Jungseong → Direction
  | .a   => .E
  | .ya  => .E
  | .eo  => .W
  | .yeo => .W
  | .o   => .N
  | .yo  => .N
  | .u   => .S
  | .yu  => .S
  | .eu  => .Hold
  | .i   => .Hold
  | .ae  => .NE
  | .e   => .NW
  | .oe  => .N
  | .wi  => .S
  | .ui  => .Hold
  | .wa  => .NE
  | .wae => .NE
  | .wo  => .SW
  | .we  => .SW
  | .ye  => .N
  | .yae => .E

def syllableDirection (s : Syllable) : Direction :=
  directionOfVowel s.v

theorem directionOfVowel_total (v : Jungseong) : ∃ d, directionOfVowel v = d :=
  ⟨directionOfVowel v, rfl⟩

theorem syllableDirection_def (s : Syllable) :
    syllableDirection s = directionOfVowel s.v := rfl

end UEM
