module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjIntegralGaloisRepStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStableCharacterFlagOfCharpolyFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDdREqOfEquiv
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaximalIdealIffNormLtOne
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFiniteExtensionGaloisRepsCharacters

section

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

noncomputable section

namespace GlobalTheory.RepFinExtJoint

theorem characterAsRankOneRep_entry {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) (g : Γ) :
    ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 = ((χ g : Kˣ) : K) := by
  simp [GlobalTheory.TripleGal.rk1, Matrix.scalar_apply]

theorem exists_finExt_chars (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] {ι : Type} (χ : ι → G E Ω →* (PadicAlgCl l)ˣ)
    (hχ : ∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) (S : Finset ι) (L₀ : FinExt l) :
    ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ s ∈ S, ∀ g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ L.1 := by
  classical
  induction S using Finset.induction_on generalizing L₀ with
  | empty => exact ⟨L₀, le_rfl, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | insert i S hi ih =>
    obtain ⟨L₁, h01, h1⟩ := ih L₀
    obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1
      (GlobalTheory.TripleGal.rk1 (χ i)) (Units.continuous_val.comp (hχ i)) L₁
    refine ⟨L₂, h01.trans h12, fun s hs g => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · have := h2 g 0 0
      rwa [characterAsRankOneRep_entry] at this
    · exact h12 (h1 s hs g)

theorem exists_finExt_root_emb (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ L : FinExt l, (∃ ζ : ↥L.1, IsPrimitiveRoot ζ l) ∧ ∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ L.1 := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ l := HasEnoughRootsOfUnity.prim
  let b := Module.finBasis ℚ E
  haveI : Fintype (E →+* PadicAlgCl l) := Fintype.ofFinite _
  let T : Finset (PadicAlgCl l) :=
    insert ζ (Finset.univ.image fun p : (E →+* PadicAlgCl l) × Fin (Module.finrank ℚ E) => p.1 (b p.2))
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hT : ∀ x ∈ T, x ∈ K := fun x hx => IntermediateField.subset_adjoin _ _ hx
  refine ⟨⟨K, inferInstance⟩, ⟨⟨ζ, hT _ (Finset.mem_insert_self _ _)⟩, ?_⟩, fun τ x => ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective (f := K.val) (by simpa using hζ) K.val.injective

  · rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact SubfieldClass.qsmul_mem K _ (hT _ (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩)))

theorem finext_joint : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  intro E Ω _ _ _ _ _ l _ n a t r ρ χ hr hρ hχ
  obtain ⟨L₀, ⟨ζ, hζ⟩, hemb⟩ := exists_finExt_root_emb E l
  obtain ⟨L₁, h01, h1⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) n r
    (Units.continuous_val.comp hr) L₀
  obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a ρ
    (Units.continuous_val.comp hρ) L₁
  obtain ⟨L₃, h23, h3⟩ := exists_finExt_chars E Ω l χ hχ Finset.univ L₂
  refine ⟨L₃, ⟨⟨ζ, h23 (h12 (h01 ζ.2))⟩, ?_⟩, fun τ x => h23 (h12 (h01 (hemb τ x))),
    fun g i j => h23 (h12 (h1 g i j)), fun g i j => h23 (h2 g i j), fun s g => h3 s (Finset.mem_univ s) g⟩
  have h0 : IsPrimitiveRoot ((ζ : ↥L₀.1) : PadicAlgCl l) l :=
    hζ.map_of_injective (f := L₀.1.val) L₀.1.val.injective
  exact IsPrimitiveRoot.of_map_of_injective (f := L₃.1.val) h0 L₃.1.val.injective

end GlobalTheory.RepFinExtJoint
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFiniteExtensionGaloisRepsCharactersStatement

section

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  first | exact @GlobalTheory.RepFinExtJoint.finext_joint | exact GlobalTheory.RepFinExtJoint.finext_joint | (intros; apply GlobalTheory.RepFinExtJoint.finext_joint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFlagLiftOfResidue

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem integral_flag_lift_of_residue : ∀ (O Γ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) O) (ρ : Γ →* GL (Fin a) O) (ψ : Fin t → Γ →* Oˣ) (ϖ : O), Irreducible ϖ → a + t = n → (∀ g m, ((r g : Matrix (Fin n) (Fin n) O).charpoly - (ρ g : Matrix (Fin a) (Fin a) O).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : Oˣ) : O))).coeff m ∈ IsLocalRing.maximalIdeal O) → (∀ (k Γ : Type) [Field k] [Group Γ] (n a t : ℕ) (r : Γ →* GL (Fin n) k) (ρ : Γ →* GL (Fin a) k) (ψ : Fin t → Γ →* kˣ), a + t = n → (∀ g, (r g : Matrix (Fin n) (Fin n) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : kˣ) : k))) → ∃ (R : ℕ) (V : Fin (R + 1) → Submodule k (Fin n → k)) (rs : Fin t → Fin R), V 0 = ⊥ ∧ V (Fin.last R) = ⊤ ∧ Monotone V ∧ (∀ g j x, x ∈ V j → (r g : Matrix (Fin n) (Fin n) k).mulVec x ∈ V j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ V (rs s).succ, x ∉ V (rs s).castSucc ∧ V (rs s).succ = V (rs s).castSucc ⊔ Submodule.span k {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) k).mulVec x - ((ψ s g : kˣ) : k) • x ∈ V (rs s).castSucc) → ∃ (R : ℕ) (M : Fin (R + 1) → Submodule O (Fin n → O)) (rs : Fin t → Fin R), (∀ x, x ∈ M 0 ↔ ∃ y : Fin n → O, x = fun i => ϖ * y i) ∧ M (Fin.last R) = ⊤ ∧ Monotone M ∧ (∀ g j x, x ∈ M j → (r g : Matrix (Fin n) (Fin n) O).mulVec x ∈ M j) ∧ Function.Injective rs ∧ ∀ s, ∃ x ∈ M (rs s).succ, x ∉ M (rs s).castSucc ∧ M (rs s).succ = M (rs s).castSucc ⊔ Submodule.span O {x} ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) O).mulVec x - (fun i => ((ψ s g : Oˣ) : O) * x i) ∈ M (rs s).castSucc := by
  intro O Γ _ _ _ _ n a t r ρ ψ ϖ hϖ hat hcong hfield
  let k := IsLocalRing.ResidueField O
  let f : O →+* k := IsLocalRing.residue O
  let rk : Γ →* GL (Fin n) k := (Matrix.GeneralLinearGroup.map f).comp r
  let ρk : Γ →* GL (Fin a) k := (Matrix.GeneralLinearGroup.map f).comp ρ
  let ψk : Fin t → Γ →* kˣ := fun s => (Units.map f.toMonoidHom).comp (ψ s)
  have hrk : ∀ g, (rk g : Matrix (Fin n) (Fin n) k) = (r g : Matrix (Fin n) (Fin n) O).map f :=
    fun g => Matrix.GeneralLinearGroup.val_map_apply f (r g)
  have hρk : ∀ g, (ρk g : Matrix (Fin a) (Fin a) k) = (ρ g : Matrix (Fin a) (Fin a) O).map f :=
    fun g => Matrix.GeneralLinearGroup.val_map_apply f (ρ g)
  have hψk : ∀ s g, ((ψk s g : kˣ) : k) = f ((ψ s g : Oˣ) : O) := fun s g => rfl
  have hchar : ∀ g, (rk g : Matrix (Fin n) (Fin n) k).charpoly
      = (ρk g : Matrix (Fin a) (Fin a) k).charpoly * ∏ s, (X - C ((ψk s g : kˣ) : k)) := by
    intro g
    rw [hrk, hρk, Matrix.charpoly_map, Matrix.charpoly_map]
    simp_rw [hψk]
    have hp : ∏ s, (X - C (f ((ψ s g : Oˣ) : O)))
        = (∏ s, (X - C ((ψ s g : Oˣ) : O))).map f := by
      simp [Polynomial.map_prod]
    rw [hp, ← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub]
    ext m
    rw [coeff_map, coeff_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hcong g m)
  obtain ⟨R, V, rs, hV0, hVtop, hVmono, hVstab, hrs, hstep⟩ :=
    hfield k Γ n a t rk ρk ψk hat hchar
  let π : (Fin n → O) →ₗ[O] (Fin n → k) := (Algebra.linearMap O k).compLeft (Fin n)
  have hπ : ∀ x i, π x i = f (x i) := fun x i => rfl
  have hπsurj : ∀ y : Fin n → k, ∃ x, π x = y := by
    intro y
    choose x hx using fun i => IsLocalRing.residue_surjective (y i)
    exact ⟨x, funext hx⟩
  have hπmul : ∀ g x, π ((r g : Matrix (Fin n) (Fin n) O).mulVec x)
      = (rk g : Matrix (Fin n) (Fin n) k).mulVec (π x) := by
    intro g x; funext i; rw [hπ, RingHom.map_mulVec, hrk]; rfl
  let M : Fin (R + 1) → Submodule O (Fin n → O) := fun j => ((V j).restrictScalars O).comap π
  have hM : ∀ j x, x ∈ M j ↔ π x ∈ V j := fun j x => Iff.rfl
  have hMmono : Monotone M := fun i j hij x hx => hVmono hij hx
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  refine ⟨R, M, rs, ?_, ?_, hMmono, ?_, hrs, ?_⟩
  · intro x
    rw [hM, hV0, Submodule.mem_bot]
    constructor
    · intro hx
      have : ∀ i, ∃ y, x i = ϖ * y := by
        intro i
        have h1 : x i ∈ IsLocalRing.maximalIdeal O := by
          rw [← IsLocalRing.residue_eq_zero_iff]; exact congr_fun hx i
        rw [hmax, Ideal.mem_span_singleton] at h1
        obtain ⟨y, hy⟩ := h1
        exact ⟨y, hy⟩
      choose y hy using this
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      show f (ϖ * y i) = 0
      rw [map_mul, (IsLocalRing.residue_eq_zero_iff ϖ).mpr (by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ), zero_mul]
  · ext x
    simp only [hM, hVtop, Submodule.mem_top]
  · intro g j x hx
    rw [hM, hπmul]
    exact hVstab g j _ hx
  · intro s
    obtain ⟨xb, hxb, hxbn, hsup, hchi⟩ := hstep s
    obtain ⟨x, rfl⟩ := hπsurj xb
    refine ⟨x, hxb, hxbn, ?_, ?_⟩
    · apply le_antisymm
      · intro y hy
        rw [hM, hsup, Submodule.mem_sup] at hy
        obtain ⟨v, hv, w, hw, hvw⟩ := hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
        rw [Submodule.mem_sup]
        refine ⟨y - c' • x, ?_, c' • x, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x),
          sub_add_cancel _ _⟩
        rw [hM, map_sub, map_smul, ← hvw]
        convert hv using 1
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        change v i + f c' * π x i - (algebraMap O k) c' * π x i = v i
        rw [show algebraMap O k = f from IsLocalRing.ResidueField.algebraMap_eq O]
        exact add_sub_cancel_right _ _
      · refine sup_le (hMmono (Fin.castSucc_le_succ _)) ?_
        rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hxb
    · intro g
      rw [hM, map_sub, hπmul]
      convert hchi g using 2
      ext i
      simp [hπ, hψk, map_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftIntSpec

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

namespace GlobalTheory.IntDescend

theorem lift_units {Γ A B : Type} [Group Γ] [Monoid A] [Monoid B] (φ : A →* B) (hφ : Function.Injective φ)
    (f : Γ →* Bˣ) (hf : ∀ g, ((f g : Bˣ) : B) ∈ Set.range φ) : ∃ f' : Γ →* Aˣ, (Units.map φ).comp f' = f := by
  classical
  have h1 : ∀ g, φ (Function.invFun φ ((f g : Bˣ) : B)) = f g := fun g => Function.invFun_eq (hf g)
  have hu : ∀ g, Function.invFun φ ((f g : Bˣ) : B) * Function.invFun φ ((f g⁻¹ : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, mul_inv_cancel, map_one f, Units.val_one]
  have hv : ∀ g, Function.invFun φ ((f g⁻¹ : Bˣ) : B) * Function.invFun φ ((f g : Bˣ) : B) = 1 := by
    intro g
    apply hφ
    rw [map_mul φ, h1, h1, map_one φ, ← Units.val_mul, ← map_mul f, inv_mul_cancel, map_one f, Units.val_one]
  refine ⟨MonoidHom.mk' (fun g => ⟨Function.invFun φ ((f g : Bˣ) : B), Function.invFun φ ((f g⁻¹ : Bˣ) : B), hu g, hv g⟩) ?_, ?_⟩
  · intro a b
    apply Units.ext
    apply hφ
    change φ (Function.invFun φ ((f (a * b) : Bˣ) : B)) = φ (Function.invFun φ ((f a : Bˣ) : B) * Function.invFun φ ((f b : Bˣ) : B))
    rw [h1, map_mul φ, h1, h1, map_mul f, Units.val_mul]
  · ext g
    exact h1 g

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

def liftInt (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) : ↥(OL LL) :=
  ⟨⟨x, hx.1⟩, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l LL ⟨x, hx.1⟩).2 hx.2⟩

theorem liftInt_spec (x : PadicAlgCl l) (hx : x ∈ LL.1 ∧ ‖x‖ ≤ 1) :
    ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) (liftInt LL x hx) = x := rfl

theorem incl_injective : Function.Injective ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

end GlobalTheory.IntDescend

namespace GlobalTheory.IntDescend

theorem descend : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (Γ : Type) [Group Γ], (∀ (n : ℕ) (f : Γ →* GL (Fin n) (PadicAlgCl l)), (∀ g i j, (f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1 ∧ ‖(f g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ 1) → ∃ f' : Γ →* GL (Fin n) ↥(OL LL), (Matrix.GeneralLinearGroup.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom))).comp f' = f) ∧ ∀ χ : Γ →* (PadicAlgCl l)ˣ, (∀ g, ((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 ∧ ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1) → ∃ ψ : Γ →* (↥(OL LL))ˣ, (Units.map ((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).toMonoidHom).comp ψ = χ := by
  intro l _ LL Γ _
  refine ⟨?_, ?_⟩
  · intro n f hf
    have hinj : Function.Injective
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro M N h
      refine Matrix.ext fun i j => ?_
      apply incl_injective LL
      have := congrArg (fun P : Matrix (Fin n) (Fin n) (PadicAlgCl l) => P i j) h
      simpa only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] using this
    have hr : ∀ g, ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) ∈ Set.range
        ((((LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)).mapMatrix : Matrix (Fin n) (Fin n) ↥(OL LL) →+* Matrix (Fin n) (Fin n) (PadicAlgCl l)).toMonoidHom) := by
      intro g
      refine ⟨Matrix.of fun i j => liftInt LL _ (hf g i j), ?_⟩
      ext i j
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      exact liftInt_spec LL _ (hf g i j)
    exact lift_units _ hinj f hr
  · intro χ hχ
    refine lift_units _ (incl_injective LL) χ ?_
    intro g
    exact ⟨liftInt LL _ ⟨(hχ g).1, (hχ g).2.le⟩, liftInt_spec LL _ _⟩

end GlobalTheory.IntDescend
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOneStatement

section

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : G E Ω →* (PadicAlgCl l)ˣ), Continuous (GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  first | exact @GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | exact GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | (intros; apply GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPair

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.WachBlock

theorem integralBlock_of_blockPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  intro E Ω _ _ _ _ _ l _ n t J bot hB
  obtain ⟨r, a, ρ, χ, hat, hr, hρ, hχ, hcong⟩ := hB
  obtain ⟨LL, hζ, hτ, hrL, hρL, hχL⟩ := GlobalTheory.T.exists_common_finiteExtension_galoisReps_characters E Ω l n a t r ρ χ hr.1 hρ (fun s => (hχ s).1)
  obtain ⟨A, hA1, hA2, hAr⟩ := GlobalTheory.T.exists_conj_integral_galoisRep E Ω l n LL r hr.1 hrL
  obtain ⟨B, hB1, hB2, hBρ⟩ := GlobalTheory.T.exists_conj_integral_galoisRep E Ω l a LL ρ hρ hρL
  have memLL : ∀ {m : ℕ} (X Y Z : Matrix (Fin m) (Fin m) (PadicAlgCl l)), (∀ i j, X i j ∈ LL.1) →
      (∀ i j, Y i j ∈ LL.1) → (∀ i j, Z i j ∈ LL.1) → ∀ i j, (X * Y * Z) i j ∈ LL.1 := by
    intro m X Y Z hX hY hZ i j
    simp only [Matrix.mul_apply]
    exact LL.1.sum_mem fun k _ => LL.1.mul_mem (LL.1.sum_mem fun k' _ => LL.1.mul_mem (hX _ _) (hY _ _)) (hZ _ _)
  have cj : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (x : GL (Fin m) (PadicAlgCl l)),
      (((MulAut.conj C⁻¹).toMonoidHom x : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) =
        ((C⁻¹ * x * C : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) := by
    intro m C x
    simp [MulAut.conj_apply]
  obtain ⟨r', hr'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 n ((MulAut.conj A⁻¹).toMonoidHom.comp r) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hAr g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hA2 (hrL g) hA1 i j)
  obtain ⟨ρ', hρ'⟩ := (GlobalTheory.IntDescend.descend l LL (G E Ω)).1 a ((MulAut.conj B⁻¹).toMonoidHom.comp ρ) (fun g i j => by
    rw [MonoidHom.comp_apply, cj]
    refine ⟨?_, hBρ g i j⟩
    simpa [Units.val_mul] using memLL _ _ _ hB2 (hρL g) hB1 i j)
  choose ψ hψ using fun s => (GlobalTheory.IntDescend.descend l LL (G E Ω)).2 (χ s) (fun g => ⟨hχL s g, GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one E Ω l (χ s) (hχ s).1 g⟩)
  haveI : IsDiscreteValuationRing ↥(OL LL) := Examples₂.LB.OL_dvr LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hmat : ∀ g, (r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((A⁻¹ * r g * A : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin n) (PadicAlgCl l) => ((f g : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l))) hr'
  have hmatρ : ∀ g, (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).map (GlobalTheory.WachBlock.ofOL l LL) =
      ((B⁻¹ * ρ g * B : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro g
    rw [← cj]
    exact congrArg (fun f : G E Ω →* GL (Fin a) (PadicAlgCl l) => ((f g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) hρ'
  have hψv : ∀ s g, GlobalTheory.WachBlock.ofOL l LL ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)) = ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    intro s g
    exact congrArg (fun f : G E Ω →* (PadicAlgCl l)ˣ => ((f g : (PadicAlgCl l)ˣ) : PadicAlgCl l)) (hψ s)
  have hcp : ∀ {m : ℕ} (C : GL (Fin m) (PadicAlgCl l)) (N : Matrix (Fin m) (Fin m) (PadicAlgCl l)),
      (((C⁻¹ : GL (Fin m) (PadicAlgCl l)) : Matrix (Fin m) (Fin m) (PadicAlgCl l)) * N * (C : Matrix (Fin m) (Fin m) (PadicAlgCl l))).charpoly = N.charpoly := by
    intro m C N
    simpa using Matrix.charpoly_units_conj C⁻¹ N
  have hc : ∀ g m, ((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    intro g m
    rw [GlobalTheory.IntMaxFinExt.mem_maximalIdeal_iff_norm_lt_one]
    have e : GlobalTheory.WachBlock.ofOL l LL (((r' g : Matrix (Fin n) (Fin n) ↥(OL LL)).charpoly - (ρ' g : Matrix (Fin a) (Fin a) ↥(OL LL)).charpoly *
      ∏ s, (Polynomial.X - Polynomial.C ((ψ s g : (↥(OL LL))ˣ) : ↥(OL LL)))).coeff m) =
        ((r g).val.charpoly - (ρ g).val.charpoly * ∏ s, (Polynomial.X - Polynomial.C ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l))).coeff m := by
      rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map,
        ← Matrix.charpoly_map, hmat, hmatρ]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hψv, Units.val_mul]
      rw [hcp, hcp]
    have h := hcong g m
    rw [← e] at h
    exact h
  obtain ⟨R, M, rs, hM0, hML, hMm, hMs, hrs, hline⟩ := GlobalTheory.integral_flag_lift_of_residue ↥(OL LL) (G E Ω) n a t r' ρ' ψ ϖ hϖ hat hc GlobalTheory.T.exists_stable_character_flag_of_charpoly_factor
  refine ⟨LL, r', ψ, ϖ, R, M, rs, hζ, hτ, ?_, fun s => ?_, hϖ, hM0, hML, hMm, hMs, hrs, hline⟩
  · have : (Matrix.GeneralLinearGroup.map (GlobalTheory.WachBlock.ofOL l LL)).comp r' = (MulAut.conj A⁻¹).toMonoidHom.comp r := hr'
    rw [this]
    exact GlobalTheory.crysWith_conj E Ω l n r A LL _ (fun i j => ⟨hA1 i j, hA2 i j⟩) hr
  · have : (Units.map (GlobalTheory.WachBlock.ofOL l LL).toMonoidHom).comp (ψ s) = χ s := hψ s
    rw [this]
    exact hχ s

end GlobalTheory.WachBlock

end
end
end
