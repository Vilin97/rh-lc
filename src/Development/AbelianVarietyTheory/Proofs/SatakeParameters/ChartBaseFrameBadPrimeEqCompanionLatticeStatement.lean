module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionHermitianLatticeFgStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeAdelicLatticeLocalizationEqStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGL

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

theorem mulVec_mem_hatL_mvL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {N : ℕ} (h : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E))
    (w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) M) :
    ((ratA F h : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
      Formalism.L2.Herm.hatL (F := F) (mvL h M) := by
  unfold Formalism.L2.Herm.hatL latS at hw ⊢
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hxM, rfl⟩ := hx
    refine Submodule.subset_span ⟨(h : Matrix (Fin N) (Fin N) E) *ᵥ x, ?_, ?_⟩
    · exact ⟨x, hxM, rfl⟩
    · exact (bc_mulVec (F := F) h x).symm
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ s ha

theorem mvL_one_lat {E : Type} [Field E] [NumberField E] {N : ℕ} (M : Submodule (𝓞 E) (Fin N → E)) : mvL 1 M = M := by
  unfold mvL
  ext x
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, h⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y = x at h
    rw [Units.val_one, Matrix.one_mulVec] at h
    simpa [h] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    change ((1 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x = x
    rw [Units.val_one, Matrix.one_mulVec]

theorem latAd_mul_ratA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)),
    latAd (y * ratA F g) M = latAd y (mvL g M) := by
  intro F E _ _ _ _ _ _ N y g M
  have key : ∀ w : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      ((ratA F g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ w ∈
        Formalism.L2.Herm.hatL (F := F) M ↔ w ∈ Formalism.L2.Herm.hatL (F := F) (mvL g M) := by
    intro w
    constructor
    · intro hw
      have := mulVec_mem_hatL_mvL g M _ hw
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.one_mulVec] at this
    · intro hw
      have := mulVec_mem_hatL_mvL g⁻¹ (mvL g M) w hw
      rwa [← mvL_mul, inv_mul_cancel, mvL_one_lat] at this
  unfold latAd
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← map_inv, key]

end GlobalTheory.TwV
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointLatticeMulRationalGLStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicPointLattice_mul_rationalGL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), latAd (y * ratA F g) M = latAd y (mvL g M) := by
  first | exact @GlobalTheory.TwV.latAd_mul_ratA | exact GlobalTheory.TwV.latAd_mul_ratA | (intros; apply GlobalTheory.TwV.latAd_mul_ratA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ), 1 ≤ d → ∀ (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), M.FG → Submodule.span E (M : Set (Fin N → E)) = ⊤ → CongAt (F := F) P d (y⁻¹ * ratA F R) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = stdAt E N P := by
  first | exact @GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | exact GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | (intros; apply GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalization

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrameLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by funext l; simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

theorem seamVec_apply {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (x : Sp X.E n) (l : Fin n) :
    seamVec s n x l = s.iE (x l) := rfl

theorem seamVec_injective {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) : Function.Injective (seamVec s n) := by
  intro x y hxy
  funext l
  exact s.iE.injective (congrFun hxy l)

theorem seam_lat_eq_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    s.lat M = M.map (seamVec s n) := by
  unfold Seam.lat
  rw [show ((fun (x : Sp X.E n) (i : Fin n) => s.iE (x i)) '' (M : Set (Sp X.E n))) = seamVec s n '' M from rfl,
    ← Submodule.map_coe]
  exact Submodule.span_eq _

theorem localization_map_seamVec {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E))
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (M.map (seamVec s n)) = (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M).map (seamVec s n) := by
  set ψ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE with hψ
  ext x
  constructor
  · rintro ⟨r, hr, z, hz, hzx⟩
    have hfy : seamVec s n (fun l => s.iE.symm (x l)) = x := by
      funext l
      simp [seamVec_apply]
    refine ⟨fun l => s.iE.symm (x l), ⟨ψ.symm r, ?_, ?_⟩, hfy⟩
    · intro hm
      apply hr
      have := (mem_seamP s P (ψ.symm r)).2 hm
      simpa [ψ] using this
    · have : ψ.symm r • (fun l => s.iE.symm (x l)) = z := by
        apply seamVec_injective s n
        rw [(seamVec s n).map_smulₛₗ, hfy, hzx]
        show ψ (ψ.symm r) • x = r • x
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact hz
  · rintro ⟨y, ⟨r, hr, hy⟩, rfl⟩
    refine ⟨ψ r, ?_, r • y, hy, ?_⟩
    · intro hm
      exact hr ((mem_seamP s P r).1 hm)
    · rw [(seamVec s n).map_smulₛₗ]
      rfl

theorem stdLat_map_seamVec {D : D7} {X : Fields} (s : Seam D X) (n : ℕ) :
    (stdLat X.E n).map (seamVec s n) = stdLat D.host.E n := by
  ext y
  rw [Submodule.mem_map]
  unfold Formalism.L2.Col.stdLat
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨x, hx, rfl⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hx l)
    refine (Submodule.mem_one).2 ⟨RingOfIntegers.mapRingEquiv s.iE r, ?_⟩
    rw [seamVec_apply, ← hr]
    rfl
  · intro hy
    refine ⟨fun l => s.iE.symm (y l), fun l => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hy l)
      refine (Submodule.mem_one).2 ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r, ?_⟩
      show _ = s.iE.symm (y l)
      rw [← hr]
      rfl
    · funext l
      simp [seamVec_apply]

theorem mvL_seamGL_map {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (M : Submodule (𝓞 X.E) (Sp X.E n)) :
    mvL (seamGL s g) (M.map (seamVec s n)) = (M.map (g.toLinearMap.restrictScalars (𝓞 X.E))).map (seamVec s n) := by
  unfold mvL
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨g x, ⟨x, hx, rfl⟩, ?_⟩
    show seamVec s n (g x) = toLE (seamGL s g) (seamVec s n x)
    rw [toLE_apply]
    exact (seamGL_mulVec s g x).symm
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨seamVec s n x, ⟨x, hx, rfl⟩, ?_⟩
    show toLE (seamGL s g) (seamVec s n x) = seamVec s n (g x)
    rw [toLE_apply]
    exact seamGL_mulVec s g x

theorem seamGL_stdAt : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) →
    mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  intro D X s n P g N hg
  have hstd : (stdAt X.E n P).map (g.toLinearMap.restrictScalars (𝓞 X.E)) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg x).2 hx
    · intro hy
      refine ⟨g.symm y, (hg _).1 (by simpa using hy), by simp⟩
  show mvL (seamGL s g) (Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (stdLat D.host.E n)) = _
  rw [← stdLat_map_seamVec s n, localization_map_seamVec, mvL_seamGL_map, ← stdAt, hstd, seam_lat_eq_map, localization_map_seamVec]

end GlobalTheory.FrameLat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedFrameStandardLocalEqLocalizationStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.transportedFrame_standardLocal_eq_localization : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (N : Submodule (𝓞 X.E) (Sp X.E n)), (∀ x, g x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ stdAt X.E n P) → mvL (seamGL s g) (stdAt D.host.E n (seamP s P)) = Formalism.HermitianLatticesTheory.localization₂ (seamP s P).asIdeal (s.lat N) := by
  first | exact @GlobalTheory.FrameLat.seamGL_stdAt | exact GlobalTheory.FrameLat.seamGL_stdAt | (intros; apply GlobalTheory.FrameLat.seamGL_stdAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLattice

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseFrameLat

theorem locP_map_equiv' {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (e : W ≃ₗ[R] W') (q : Ideal R) [q.IsPrime] (Λ : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ q (Λ.map (e : W →ₗ[R] W')) = (Formalism.HermitianLatticesTheory.localization₂ q Λ).map (e : W →ₗ[R] W') := by
  ext x
  constructor
  · rintro ⟨s, hs, z, hz, hzx⟩
    refine ⟨e.symm x, ⟨s, hs, ?_⟩, by simp⟩
    have : s • e.symm x = z := by
      apply e.injective
      rw [map_smul, e.apply_symm_apply]
      exact hzx.symm
    rw [this]
    exact hz
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨s, hs, s • y, hy, by simp⟩

theorem locP_mvL_comm {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ : Submodule (𝓞 E) (Fin N → E)) : Formalism.HermitianLatticesTheory.localization₂ q (mvL c Λ) = mvL c (Formalism.HermitianLatticesTheory.localization₂ q Λ) :=
  locP_map_equiv' ((toLE c).restrictScalars (𝓞 E)) q Λ

theorem mvL_one' {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (Λ : Submodule (𝓞 E) (Fin N → E)) : mvL 1 Λ = Λ := by
  unfold mvL
  convert Submodule.map_id _
  refine LinearMap.ext fun z => ?_
  show toLE 1 z = z
  rw [toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem span_mvL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (c : GL (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (h : Submodule.span E (Λ : Set (Fin N → E)) = ⊤) : Submodule.span E ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = ⊤ := by
  have e : ((mvL c Λ : Submodule (𝓞 E) (Fin N → E)) : Set (Fin N → E)) = (toLE c : (Fin N → E) →ₗ[E] (Fin N → E)) '' (Λ : Set (Fin N → E)) := by
    unfold mvL
    rw [Submodule.map_coe]
    rfl
  rw [e, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top]
  exact (toLE c).surjective

end GlobalTheory.BaseFrameLat


open GlobalTheory.BaseFrameLat in
theorem GlobalTheory.TwV.baseFrame_std_eq_compan : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpins htie i hi β x p hp P
  have hd : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  have hR := GlobalTheory.T.transportedFrame_standardLocal_eq_localization t.seam P.1 (frsF t.sel (t.tup μ) p P) p.deco.1.N (GlobalTheory.TopStep.frsF_mem p P)
  rw [hp.lat] at hR
  have hJ : IsUnit (gramN D i hi).det := by
    rw [← hpins.crd_orth i hi, Matrix.det_mul]
    have hc : IsUnit ((A.crd i hi).1).det := (Matrix.isUnit_iff_isUnit_det _).mp (A.crd i hi).isUnit
    refine IsUnit.mul ?_ hc
    show IsUnit ((((A.crd i hi).1).map (sigD D : D.host.E →+* D.host.E))ᵀ).det
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hc.map _
  have hfg : (((St i hi).K β).lev.Lb).FG := Module.Finite.iff_fg.mp ((St i hi).K β).lev.Lb_fin
  have hsp := ((St i hi).K β).lev.Lb_span
  have h4 := GlobalTheory.T.companionLattice_adelicLattice_localization_eq D.sp (sigD D) rfl (gramN D i hi) hJ a x.1 x.2 _ hfg hsp (seamP t.seam P.1)
  have hCfg := GlobalTheory.T.companionHermitianLattice_fg D.sp (gramN D i hi) hJ a _ hfg hsp
  set C := compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb with hC
  have hCs : Submodule.span D.host.E (C : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
    refine eq_top_iff.2 (hsp ▸ Submodule.span_mono ?_)
    intro z hz
    exact (le_sup_left : ((St i hi).K β).lev.Lb ≤ C) hz
  unfold latCo at hR
  rw [locP_mvL_comm, h4, ← locP_mvL_comm] at hR
  have e1 : mvL (A.crd i hi) (latAd x.1 C) = latAd (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (mvL (A.fb i hi β P)⁻¹ C) := by
    rw [GlobalTheory.T.adelicPointLattice_mul_rationalGL, ← mvL_mul, mul_inv_cancel, mvL_one']
    exact (latAd_rat _ _ _).symm
  rw [e1] at hR
  have h3 := GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime (seamP t.seam P.1) _ hd _ _ (mvL (A.fb i hi β P)⁻¹ C) (hCfg.map _) (span_mvL _ _ hCs) (hp.frame P) hR.symm
  rw [← h3, ← locP_mvL_comm, ← mvL_mul, mul_inv_cancel, mvL_one']
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseFrameBadPrimeEqCompanionLatticeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartBaseFrame_badPrime_eq_companion_lattice : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) p, IsPtAd A a i hi β x p → ∀ P : SB t μ, mvL (A.fb i hi β P) (stdAt D.host.E (D.R.N i) (seamP t.seam P.1)) = Formalism.HermitianLatticesTheory.localization₂ (seamP t.seam P.1).asIdeal (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb)) := by
  first | exact @GlobalTheory.TwV.baseFrame_std_eq_compan | exact GlobalTheory.TwV.baseFrame_std_eq_compan | (intros; apply GlobalTheory.TwV.baseFrame_std_eq_compan <;> assumption)
end
end
