module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelObjectGlueArtinFibreProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectTangentShiftConstancyDirectionIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstant

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangentBound

def acts (W : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ
  | .inl uv => Matrix.single uv.1 uv.2 1
  | .inr true => (W + W.transpose).adjugate * W
  | .inr false => (W + W.transpose).adjugate * W.transpose

theorem main : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro h n _ h3 hodd K _ _ r β c hc hun
  have hn : n ≠ 0 := by omega
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W, hW, hbasAll⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hbasAll h
  have hζ : (cycBase hn).ζ ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, cycBase_ζ]
    exact Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
  have hdet : (W + W.transpose).det = 1 := hW.2
  have hw : (W + W.transpose) * acts W (.inr true) = W := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have hw' : (W + W.transpose) * acts W (.inr false) = W.transpose := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have he : ∀ u v : Fin 8, ∃ j, acts W j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c hodd h3 hζ hc
  refine GlobalTheory.PowerTangent.main L1 L2 GlobalTheory.Moduli.cube_of_isLB h (8 * h) W _ (acts W) bas hW hbas (.inr true) (.inr false)
    hw hw' n (cycAway n) (cycBase hn) K r β t c hc ht ?_
  intro lam t' m₁ m₂
  have hf : spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      spMap ((algebraMap K (DualNumber K)).comp β) ≫ spMap (RingHom.id (cycAway n)) := by
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => by
      simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).1 c
  have hc'P := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).2.1 c c' hc' hc
  obtain ⟨t'', ht''⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c' hodd h3 hζ hc'P
  have m₃ : TMap t'' t (spMap (dirMap lam)) :=
    (GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
      (spMap (dirMap lam)) hc hc'P ht ht'').1 hc'
  have m₄ : TMap t'' t' (𝟙 _) :=
    ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₁).2 (by rwa [Category.id_comp])
  have m₅ : TMap t'' t (constPt (spMap (dirMap lam))) := by
    have := ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₂).1 m₄
    rwa [Category.id_comp] at this
  exact hun lam c' hc' ((GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
    _ hc hc'P ht ht'').2 he m₅)

end GlobalTheory.SiegelTangentBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstantStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegelFamily_tangentBound_nonconstant : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  first | exact @GlobalTheory.SiegelTangentBound.main | exact GlobalTheory.SiegelTangentBound.main | (intros; apply GlobalTheory.SiegelTangentBound.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToDualNumbers

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.FirstOrderSiegel

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

variable {h k : ℕ}

theorem isLocalRing_tsze (K : Type) [Field K] (r : ℕ) : IsLocalRing (TrivSqZeroExt K (Fin r → K)) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_tsze (K : Type) [Field K] (r : ℕ) : IsArtinianRing (TrivSqZeroExt K (Fin r → K)) :=
  haveI : Module.Finite K (TrivSqZeroExt K (Fin r → K)) := inferInstanceAs (Module.Finite K (K × (Fin r → K)))
  IsArtinianRing.of_finite K _

theorem pull_exists {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B}
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ (c.Principal → c'.Principal) := by
  have e : f ≫ s = s' ≫ spMap (RingHom.id B) := by
    rw [hf]
    simp [spMap]
  have H := siegPre_pull_ringChange h k B B ζ ζ (RingHom.id B) S S' s s' f rfl e
  obtain ⟨c', hc'⟩ := H.1 c
  exact ⟨c', hc', H.2.1 c c' hc'⟩

theorem pb_symm {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}} {s : S ⟶ Sp B}
    {s' : S ⟶ Sp B'} {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} (m : SiegPB c' c (𝟙 S)) : SiegPB c c' (𝟙 S) :=
  pb_cancel m (by rw [Category.comp_id]; exact pb_id c)

theorem constPt_comp {K : Type} [Field K] {X Y : Scheme.{0}} (x : Sp (DualNumber K) ⟶ X) (z : X ⟶ Y) :
    constPt (x ≫ z) = constPt x ≫ z := by
  unfold constPt
  simp only [Category.assoc]

theorem base_map {K o V W : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W] (β : o →+* K)
    (L : V →ₗ[K] W) : spMap (TrivSqZeroExt.map L).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) =
      spMap ((algebraMap K (TrivSqZeroExt K W)).comp β) := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.map L).commutes (β z)

theorem fst_base {K o V : Type} [Field K] [CommRing o] [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] (β : o →+* K) :
    spMap (TrivSqZeroExt.fstHom K K V).toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K V)).comp β) = spMap β := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun z => (TrivSqZeroExt.fstHom K K V).commutes (β z)

theorem constPt_base {K o : Type} [Field K] [CommRing o] {X : Scheme.{0}} (β : o →+* K) (x : Sp (DualNumber K) ⟶ X)
    (s : X ⟶ Sp o) (hx : x ≫ s = spMap ((algebraMap K (DualNumber K)).comp β)) :
    constPt x ≫ s = x ≫ s := by
  unfold constPt
  rw [Category.assoc, Category.assoc, hx, fst_base, ← spMap_comp']

theorem dirMap_comp {K : Type} [Field K] {r m : ℕ} (mu : (Fin m → K) →ₗ[K] K) (L : (Fin r → K) →ₗ[K] (Fin m → K)) :
    spMap (dirMap (mu ∘ₗ L)) = spMap (dirMap mu) ≫ spMap (TrivSqZeroExt.map L).toRingHom := by
  rw [← spMap_comp']
  congr 1 <;> exact RingHom.ext fun x => TrivSqZeroExt.ext (by simp [dirMap]) (by simp [dirMap])

def drop (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) := GlobalTheory.InnerAutomorphism.dropLast K d

def lastC (K : Type) [Field K] (d : ℕ) : (Fin (d + 1) → K) →ₗ[K] K := LinearMap.proj (Fin.last d)

def incl (K : Type) [Field K] (d : ℕ) : (Fin d → K) →ₗ[K] (Fin (d + 1) → K) where
  toFun w := Fin.snoc w 0
  map_add' w w' := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a w := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem bij_drop_last (K : Type) [Field K] (d : ℕ) : Function.Bijective ((drop K d).prod (lastC K d)) := by
  refine ⟨fun v w hvw => ?_, fun p => ⟨Fin.snoc p.1 p.2, ?_⟩⟩
  · have h1 := congrArg Prod.fst hvw
    have h2 := congrArg Prod.snd hvw
    simp only [LinearMap.prod_apply] at h1 h2
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact h2
    · exact congrFun h1 j
  · ext j <;> simp [drop, lastC, GlobalTheory.InnerAutomorphism.dropLast]

theorem lam_decomp (K : Type) [Field K] (d : ℕ) (lam : (Fin (d + 1) → K) →ₗ[K] K) :
    lam = (lam ∘ₗ incl K d) ∘ₗ drop K d + lam (Pi.single (Fin.last d) 1) • lastC K d := by
  refine LinearMap.ext fun v => ?_
  have hv : v = incl K d (drop K d v) + v (Fin.last d) • Pi.single (Fin.last d) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [incl]
    · simp [incl, drop, GlobalTheory.InnerAutomorphism.dropLast, Pi.single_apply, Fin.castSucc_ne_last]
  conv_lhs => rw [hv]
  simp [lastC, mul_comm]

theorem classified_dualNumber_of_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F K _ _ β₀ c hc

  obtain ⟨c₀, hc₀, hc₀p⟩ := pull_exists (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (fst_base β₀) c
  obtain ⟨x₀, hx₀s, hx₀⟩ := GlobalTheory.T.siegel_family_classifies_principal_algClosed g n hg hn hodd F K β₀ c₀ (hc₀p hc)

  obtain ⟨y, hy₀, hys, hyinj⟩ := GlobalTheory.T.exists_firstOrder_tangentPoint_smooth F.X F.s (g * (g + 1) / 2) F.smooth K β₀ x₀ hx₀s
  obtain ⟨cy, hcy, hcyp⟩ := pull_exists y hys F.univ
  have h0y : SiegPB c₀ cy (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) :=
    pb_cancel hcy (by rw [hy₀]; exact hx₀)

  have hsq := GlobalTheory.T.trivial_square_zero_extension_pullback K (Fin (g * (g + 1) / 2 + 1) → K) (Fin (g * (g + 1) / 2) → K) K (drop K _) (lastC K _)
    (bij_drop_last K _)
  let β : CommRingCat.of (cycAway n) ⟶ CommRingCat.of (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K)) :=
    CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (Fin (g * (g + 1) / 2 + 1) → K))).comp β₀)
  obtain ⟨c₁, hc₁, hc₁p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) cy
  obtain ⟨c₂, hc₂, hc₂p⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (lastC K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by rw [Category.id_comp]; exact (base_map β₀ _).symm) c
  obtain ⟨c₀', hc₀', -⟩ := pull_exists (𝟙 _)
    (s' := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) ≫ Spec.map β)
    (by
      rw [Category.id_comp]
      exact ((congrArg (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom ≫ ·)
        (base_map β₀ (drop K _))).trans (fst_base β₀)).symm) c₀
  have h01 : SiegPB c₀' c₁ (spMap (TrivSqZeroExt.fstHom K K (Fin (g * (g + 1) / 2) → K)).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₁) h0y) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  have h02 : SiegPB c₀' c₂ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    have := pb_comp (pb_comp (pb_symm hc₂) hc₀) hc₀'
    rwa [Category.comp_id, Category.id_comp] at this
  obtain ⟨G, hGp, hG1, hG2⟩ := GlobalTheory.T.exists_principalSiegelObject_glue_artinFibreProduct g n hn hodd _ _ (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _
    hsq (isLocalRing_tsze K _) (isArtinianRing_tsze K _) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) β c₁ c₂ (hc₁p (hcyp F.princ)) (hc₂p hc) ⟨c₀', h01, h02⟩
  have hGy : SiegPB cy G (spMap (TrivSqZeroExt.map (drop K (g * (g + 1) / 2))).toRingHom) := by
    have := pb_comp hG1 (pb_symm hc₁)
    rwa [Category.id_comp] at this
  have hGc : SiegPB c G (spMap (dirMap (lastC K (g * (g + 1) / 2)))) := by
    have := pb_comp hG2 (pb_symm hc₂)
    rwa [Category.id_comp] at this

  have htb := GlobalTheory.T.siegelFamily_tangentBound_nonconstant g n hg hn hodd K (g * (g + 1) / 2 + 1) β₀ G hGp
  obtain ⟨lam, c', h1, h2, hlam⟩ : ∃ (lam : (Fin (g * (g + 1) / 2 + 1) → K) →ₗ[K] K)
      (c' : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))),
      SiegPB c' G (spMap (dirMap lam)) ∧ SiegPB c' G (constPt (spMap (dirMap lam))) ∧ lam ≠ 0 := by
    by_contra hne
    push_neg at hne
    have := htb fun lam c' h1 h2 => hne lam c' h1 h2
    omega
  obtain ⟨mu, a, hdec⟩ : ∃ (mu : (Fin (g * (g + 1) / 2) → K) →ₗ[K] K) (a : K),
      lam = mu ∘ₗ drop K _ + a • lastC K _ := ⟨_, _, lam_decomp K _ lam⟩
  by_cases ha : a = 0
  ·
    exfalso
    rw [ha, zero_smul, add_zero] at hdec
    subst hdec
    rw [dirMap_comp] at h1 h2
    rw [constPt_comp] at h2
    have k1 : SiegPB c' F.univ (spMap (dirMap mu) ≫ y) := pb_comp hcy (pb_cancel hGy h1)
    have k2 : SiegPB c' F.univ (constPt (spMap (dirMap mu) ≫ y)) := by
      rw [constPt_comp]
      exact pb_comp hcy (pb_cancel hGy h2)
    have hxs : (spMap (dirMap mu) ≫ y) ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) := by
      rw [Category.assoc, hys]
      exact base_map β₀ mu
    obtain ⟨c'', hc'', -⟩ := pull_exists (𝟙 _) (s' := (spMap (dirMap mu) ≫ y) ≫ F.s)
      (by rw [Category.id_comp, hxs]) c'
    have e := F.eq_constPt K (spMap (dirMap mu) ≫ y) c'' (constPt_base β₀ _ _ hxs).symm
      (by have := pb_comp k1 hc''; rwa [Category.id_comp] at this)
      (by have := pb_comp k2 hc''; rwa [Category.id_comp] at this)
    have := hyinj mu e
    subst this
    exact hlam (by simp)
  ·
    have hκ : lastC K (g * (g + 1) / 2) = ((-a⁻¹) • mu) ∘ₗ drop K _ + a⁻¹ • lam := by
      rw [hdec]
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, neg_mul]
      field_simp
      ring
    have k := GlobalTheory.T.siegelObject_tangentShift_constancy_direction_iso g n hn hodd K _ β₀ G hGp lam _ _ a⁻¹ c' c hκ h1 h2 hGc
    rw [dirMap_comp] at k
    refine ⟨spMap (dirMap ((-a⁻¹) • mu)) ≫ y, ?_, pb_comp hcy (pb_cancel hGy k)⟩
    rw [Category.assoc, hys]
    exact base_map β₀ _

end GlobalTheory.FirstOrderSiegel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPointLiftsToDualNumbersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.siegel_point_lifts_to_dual_numbers : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β₀ : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β₀))), c.Principal → ∃ f : Sp (DualNumber K) ⟶ F.X, f ≫ F.s = spMap ((algebraMap K (DualNumber K)).comp β₀) ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed | exact GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed | (intros; apply GlobalTheory.FirstOrderSiegel.classified_dualNumber_of_algClosed <;> assumption)
end
end
