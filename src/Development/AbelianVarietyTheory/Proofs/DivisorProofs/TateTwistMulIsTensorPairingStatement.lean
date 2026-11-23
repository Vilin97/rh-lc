module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalPropertyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistGeneratorTmulOrderLocallyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallyInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjectiveStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHom

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem Sec.res_map_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have h := congrArg (fun h => h.hom x) (f.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem Sec.map_nsmul_of_sheaf_morphism {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul (f.hom.app (op U)).hom n x

theorem nsmul_eq_of_natCast_eq_zmod_ulift_module {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {m n : ℕ}
    (h : (m : ZMod q) = (n : ZMod q)) (x : M) : m • x = n • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) m x, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) n x]
  congr 1
  apply ULift.ext
  simpa using h

theorem twist_mul_map : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  intro q _ i j k hk K τ
  obtain ⟨-, -, -, h4i, h5i, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q i
  obtain ⟨-, -, -, h4j, h5j, -⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q j
  obtain ⟨-, -, -, -, -, h6⟩ := GlobalTheory.T.tateTwist_sections_locally_generated q k
  let e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (K.X 0) U := fun U ζ =>
    τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  have hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom) := by
    intro V U g ζ
    simp only [e]
    rw [τ.nat, Sec.res_map_of_sheaf_morphism, Sec.res_map_of_sheaf_morphism, h4i, h4j]
  have hrel : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ k : (ZMod q)ˣ) : ZMod q).val • e U ζ := by
    intro U ζ ξ a h
    simp only [e]
    rw [h5i U ζ ξ a h, h5j U ζ ξ a h, Sec.map_nsmul_of_sheaf_morphism, Sec.map_nsmul_of_sheaf_morphism, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul]
    apply nsmul_eq_of_natCast_eq_zmod_ulift_module (q := q)
    rw [Nat.cast_mul, ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id,
      ← hk, zpow_add, Units.val_mul, mul_comm]
  obtain ⟨φ, hφ, -⟩ := h6 (K.X 0) e hnat hrel
  exact ⟨φ, hφ⟩

end GlobalTheory.EtC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateTwistMulDegreeZeroHomStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), ∃ φ : tw q k ⟶ K.X 0, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) := by
  first | (exact @GlobalTheory.EtC.twist_mul_map) | (exact GlobalTheory.EtC.twist_mul_map) | (intros; apply GlobalTheory.EtC.twist_mul_map  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorOfCompatIsIsoTarget

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC

theorem Pair.isTensor_of_compat_isIso (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K')
    (u : K ⟶ K') : IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  intro hu hc hτ
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), ν.lift U w x = Sec.map (u.f w) (τ.lift U w x) := by
    intro U w x
    have h : ν.lift U w = ((u.f w).hom.app (op U)).hom ∘ₗ τ.lift U w := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
      exact (hc U p.1.1 p.1.2 w p.2 a b).symm
    exact LinearMap.congr_fun h x
  have hinv : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K'.X w) U), Sec.map (u.f w) (Sec.map ((inv u).f w) y) = y := by
    intro w U y
    change Sec.map ((inv u).f w ≫ u.f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.inv_hom_id, HomologicalComplex.id_f]
    rfl
  have hinv' : ∀ (w : ℤ) (U : Scheme.{0}) (y : Sec (K.X w) U), Sec.map ((inv u).f w) (Sec.map (u.f w) y) = y := by
    intro w U y
    change Sec.map (u.f w ≫ (inv u).f w) y = y
    rw [← HomologicalComplex.comp_f, IsIso.hom_inv_id, HomologicalComplex.id_f]
    rfl
  have hnat : ∀ {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U),
      Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
    intro F G φ V U g z
    exact congrArg (fun f => f.hom z) (φ.hom.naturality g.op)
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · obtain ⟨S, hS, hP⟩ := hτ.1 U w (Sec.map ((inv u).f w) y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    rw [hlift, hx, hnat, hinv]
  · apply hτ.2 U w x
    rw [hlift] at hx
    have h2 := congrArg (Sec.map ((inv u).f w)) hx
    rw [hinv'] at h2
    rw [h2]
    exact map_zero _

end GlobalTheory.EtC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorOfCompatIsIsoTargetStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isTensor_of_compat_isIso_target : ∀ (R : Type) [CommRing R] {I J K K' : Cx R} (τ : Pair I J K) (ν : Pair I J K') (u : K ⟶ K'), IsIso u → τ.Compat ν (𝟙 I) (𝟙 J) u → τ.IsTensor → ν.IsTensor := by
  first | (exact @GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (exact GlobalTheory.EtC.Pair.isTensor_of_compat_isIso) | (intros; apply GlobalTheory.EtC.Pair.isTensor_of_compat_isIso  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroTensorOfDegreeZeroComplexes

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TensZero

variable {R : Type} [CommRing R]

theorem sec_eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (a : Sec F U) : a = 0 := by
  have h : 𝟙 F = 0 := hF.eq_of_src _ _
  have : Sec.map (𝟙 F) a = Sec.map (0 : F ⟶ F) a := by rw [h]
  have h1 : Sec.map (𝟙 F) a = a := rfl
  have h2 : Sec.map (0 : F ⟶ F) a = 0 := by
    simp only [Sec.map]
    rfl
  rw [h1, h2] at this
  exact this

theorem isZero_of_sec {F : Shv R} (h : ∀ (U : Scheme.{0}) (a : Sec F U), a = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine ((GlobalTheory.EtC.mono_epi_sections R (𝟙 F)).2.2.2 0 fun U a => ?_)
  rw [h U a]
  simp

theorem tens_eq_zero {I J : Cx R} (hI : ∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) (hJ : ∀ t : ℤ, t ≠ 0 → IsZero (J.X t))
    (U : Scheme.{0}) (w : ℤ) (hw : w ≠ 0) (x : Tens I J U w) : x = 0 := by
  refine DFinsupp.ext fun p => ?_
  show x p = 0
  have hp := p.2
  by_cases h1 : p.1.1 = 0
  · have h2 : p.1.2 ≠ 0 := by omega
    induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hJ _ h2) b, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  · induction x p using TensorProduct.induction_on with
    | zero => rfl
    | tmul a b => rw [sec_eq_zero_of_isZero (hI _ h1) a, TensorProduct.zero_tmul]
    | add a b ha hb => rw [ha, hb, add_zero]

end GlobalTheory.EtC.TensZero

open GlobalTheory.EtC.TensZero in
theorem GlobalTheory.EtC.isZero_tensor_of_deg_zero : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  intro R _ I J K τ hτ hI hJ w hw
  refine isZero_of_sec fun U y => ?_
  refine (GlobalTheory.EtC.sec_ext_glue R (K.X w) U).1 y 0 ?_
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [tens_eq_zero hI hJ V w hw x, map_zero] at hx
  rw [← hx]
  exact (map_zero _).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroTensorOfDegreeZeroComplexesStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isZero_tensor_of_degree_zero_complexes : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ s : ℤ, s ≠ 0 → IsZero (I.X s)) → (∀ t : ℤ, t ≠ 0 → IsZero (J.X t)) → ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) := by
  first | exact @GlobalTheory.EtC.isZero_tensor_of_deg_zero | exact GlobalTheory.EtC.isZero_tensor_of_deg_zero | (intros; apply GlobalTheory.EtC.isZero_tensor_of_deg_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulIsTensorPairing

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwMul

theorem secMap_comp {R : Type} [CommRing R] {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem secMap_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem tw_mul_isTensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ) := by
  intro q _ i j k hk
  obtain ⟨K, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) (sgl (tw q j))
  have hzK : ∀ w : ℤ, w ≠ 0 → IsZero (K.X w) :=
    GlobalTheory.T.isZero_tensor_of_degree_zero_complexes (ZMod q) τ hτ (fun s hs => HomologicalComplex.isZero_single_obj_X _ _ _ _ hs)
      (fun t ht => HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_tateTwist_mul_degreeZero_hom q i j k hk τ
  have hsurj := GlobalTheory.T.tateTwist_mul_degreeZero_locally_surjective q i j k hk τ hτ φ hφ
  have hinj := GlobalTheory.T.tateTwist_mul_degreeZero_locally_injective q i j k hk (GlobalTheory.T.tateTwistGenerator_tmul_order_locally q i j) τ hτ φ hφ
  have hM := GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections (ZMod q) φ
  haveI : Mono φ := hM.2.1.2 hinj
  haveI : Epi φ := hM.2.2.1.2 hsurj
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  let u : K ⟶ sgl (tw q k) := HomologicalComplex.mkHomToSingle (inv φ) (fun a ha => (hzK a (by simp at ha; omega)).eq_of_src _ _)
  have hu0 : u.f 0 = inv φ ≫ sglι (tw q k) := HomologicalComplex.mkHomToSingle_f _ _
  haveI : ∀ w, IsIso (u.f w) := by
    intro w
    by_cases hw : w = 0
    · subst hw; rw [hu0]; unfold sglι; exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)
    · exact ⟨⟨0, (hzK w hw).eq_of_src _ _, (HomologicalComplex.isZero_single_obj_X _ _ _ _ hw).eq_of_src _ _⟩⟩
  haveI : IsIso u := HomologicalComplex.Hom.isIso_of_components u
  obtain ⟨ν, hν⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.2 u
  refine ⟨ν, GlobalTheory.T.isTensor_of_compat_isIso_target (ZMod q) τ ν u inferInstance hν hτ, fun U ζ => ?_⟩
  have h := hν U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))
  simp only [HomologicalComplex.id_f, secMap_id] at h
  rw [← h, ← hφ, hu0, secMap_comp, ← secMap_comp φ (inv φ), IsIso.hom_inv_id, secMap_id]

end GlobalTheory.EtC.TwMul
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulIsTensorPairingStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwist_mul_isTensorPairing : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ) := by
  first
  | exact @GlobalTheory.EtC.TwMul.tw_mul_isTensor
  | exact GlobalTheory.EtC.TwMul.tw_mul_isTensor
  | (intros; apply GlobalTheory.EtC.TwMul.tw_mul_isTensor <;> assumption)
end
end
