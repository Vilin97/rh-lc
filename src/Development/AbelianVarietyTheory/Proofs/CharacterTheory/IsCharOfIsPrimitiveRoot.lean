module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducibleStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAddStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePowerStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrimStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower : ∀ (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G] (χ : G → L), AbByP G → IsIrrChar L L χ → (∃ lam : G →* Lˣ, ∀ g, χ g = (lam g : L)) ∨ ∃ T : Subgroup G, T ≠ ⊤ ∧ ∃ ψ : T → L, IsChar L L ψ ∧ χ = ind T ψ := by
  first | exact @GlobalTheory.BI.irrChar_linear_or_induced | exact GlobalTheory.BI.irrChar_linear_or_induced | (intros; apply GlobalTheory.BI.irrChar_linear_or_induced <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroupStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup : ∀ (G : Type) [Group G] (T : Subgroup G), AbByP G → AbByP T := by
  first | exact @GlobalTheory.BI.AbByP.subgroup | exact GlobalTheory.BI.AbByP.subgroup | (intros; apply GlobalTheory.BI.AbByP.subgroup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRoot

section

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_linear : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  intro K L _ _ _ G _ m ζ lam hm hζ hG
  haveI : NeZero m := ⟨hm⟩
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hζ' : IsPrimitiveRoot (algebraMap K L ζ) m := hζ.map_of_injective hinj
  have h : ∀ g : G, ∃ x : K, algebraMap K L x = (lam g : L) := by
    intro g
    have h1 : (lam g : L) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, by rw [map_pow, hi]⟩
  choose μ hμ using h
  let μ' : G →* K :=
    { toFun := μ
      map_one' := hinj (by rw [hμ]; simp)
      map_mul' := fun a b => hinj (by rw [map_mul (algebraMap K L), hμ, hμ, hμ]; simp) }
  refine ⟨1, ((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ', fun g => ?_⟩
  have : Representation.character (((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ' : Representation K G (Fin 1 → K)) g = μ g := by
    change LinearMap.trace K (Fin 1 → K) (algebraMap K (Module.End K (Fin 1 → K)) (μ g)) = μ g
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one]
    simp
  rw [this, hμ]
end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRootStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  first | exact @GlobalTheory.BI.isChar_linear | exact GlobalTheory.BI.isChar_linear | (intros; apply GlobalTheory.BI.isChar_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower

section

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_abByP : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → (∀ g : G, g ^ m = 1) → AbByP G →
      ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hG hA χ hχ
      refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible L L G (fun a => IsChar K L a) (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).1 ?_ χ hχ
      intro φ c hφ _ hc
      refine (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).2 φ c ?_ hc
      rcases GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower L G φ hA hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have : φ = fun g => (lam g : L) := funext hlam
        rw [this]
        exact GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot K L G m ζ lam hm hζ hG
      · have hlt : Nat.card T < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group T)
            (fun h => hT (Subgroup.eq_top_of_card_eq T h))
        refine GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction K L G T ψ (ih _ hlt T rfl ?_ (GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup G T hA) ψ hψ)
        intro g
        exact Subtype.ext (by simpa using hG g)
  intro G _ _
  exact key _ G rfl
end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePowerStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_abByP | exact GlobalTheory.BI.isChar_of_abByP | (intros; apply GlobalTheory.BI.isChar_of_abByP <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacterStatement

section

@[expose] public section

open GlobalTheory.BI

theorem _root_.GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (χ : G → L), IsChar L L χ → χ ∈ Virt K L G → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_isChar_of_mem_virt | exact GlobalTheory.BI.isChar_of_isChar_of_mem_virt | (intros; apply GlobalTheory.BI.isChar_of_isChar_of_mem_virt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot

section

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_isPrimitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ G _ _ hG χ hχ
  refine GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character K L G χ hχ (GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower K L G (fun H hH ψ hψ => ?_) χ hχ)
  exact GlobalTheory.T.isCharacterOverSubfield_abelianByPrimePower K L m ζ hm hζ H (fun h => Subtype.ext (by simpa using hG (h : G))) hH ψ hψ
end GlobalTheory.BI
end
end
