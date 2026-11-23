module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPointsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsArtinianRingFibQuotStatement
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Ring
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSmoothFiniteCoverOfFormsNoCommonZeroStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexPointKerEvalEqMaximal

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem exists_cxPts_ker_eq : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  intro X p _ U hU m hm
  have h1 := p.finiteType_appLE (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : m.IsMaximal := hm
  letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, U) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, U) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, U) →+* ℂ := (e.symm : (Γ(X, U) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p U a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, U) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  refine ⟨CxPts.ofHom hU φ hφ, CxPts.ofHom_mem hU φ hφ, ?_⟩
  have hev : CxPts.evHom (CxPts.ofHom_mem hU φ hφ) = φ := by
    ext f
    rw [← CxPts.ev_eq, CxPts.ev_ofHom]
  rw [hev]
  ext f
  rw [RingHom.mem_ker]
  show f ∈ m ↔ e.symm (Ideal.Quotient.mk m f) = 0
  rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexPointKerEvalEqMaximalStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

theorem _root_.GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  first | (exact @GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (exact GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (intros; apply GlobalTheory.MaxPt.exists_cxPts_ker_eq  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLe

section

@[expose] public section

namespace GlobalTheory

open scoped BigOperators

theorem quotient_maximal_le_sq {A : Type} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set m := M.comap (Ideal.Quotient.mk I) with hm
  have hmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := by
    intro x hx
    simp [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have key := Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    hm, Ideal.map_comap_of_surjective _ hsurj] at key
  exact key

theorem pow_eq_self_of_le_sq {R : Type} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2) :
    ∀ k : ℕ, M ^ (k + 1) = M := by
  have h2 : M * M = M := by
    rw [← sq]; exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h2]

theorem isReduced_quotient_of_artinian_of_maximal_le (A : Type) [CommRing A] (I : Ideal A)
    (hart : IsArtinianRing (A ⧸ I))
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  classical
  set R := A ⧸ I
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ
  have hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal := by
    rw [hJ]
    apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
    intro a _ b _ hab
    exact Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))
  have hpow : ∀ k : ℕ, J ^ (k + 1) = J := by
    intro k
    rw [hJ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun M _ => ?_)
    exact pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k
  have hJjac : J ≤ Ideal.jacobson ⊥ := by
    rw [hJinf]
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    by_contra hu
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal (Ideal.span {x * y + 1})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hxM : x ∈ M := by
      have := (Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩
      simpa using this
    have h1 : x * y + 1 ∈ M := hM (Ideal.subset_span rfl)
    have : (1 : R) ∈ M := by
      have := M.sub_mem h1 (M.mul_mem_right y hxM)
      simpa using this
    exact hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hJbot : J = ⊥ := by
    rw [← hpow n]
    refine le_bot_iff.mp ?_
    calc J ^ (n + 1) ≤ (Ideal.jacobson ⊥) ^ (n + 1) := Ideal.pow_right_mono hJjac _
      _ ≤ (Ideal.jacobson ⊥) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine ⟨fun x hx => ?_⟩
  have hxJ : x ∈ J := by
    rw [hJinf]
    refine (Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))
    exact (hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hJbot] at hxJ
  exact (Submodule.mem_bot R).mp hxJ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' : ∀ (A : Type) [CommRing A] (I : Ideal A), IsArtinianRing (A ⧸ I) →
    (∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) → IsReduced (A ⧸ I) := by
  first | (exact @GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (exact GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (intros; apply GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteCoverProjSpaceReducedFibreOrigin

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.PD.FibRed

theorem quotEquiv_of_germ {X : Scheme.{0}} [IsIntegral X] [Algebra ℂ X.functionField] {F : Type} [Field F] [Algebra ℂ F]
    [Algebra F X.functionField] [IsScalarTower ℂ F X.functionField] {d : ℕ} (x : Fin (d + 1) → F) (U : X.Opens)
    (hg : genericPoint X ∈ U) (t : Fin d → Γ(X, U))
    (hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔ ∃ f : Γ(X, U), (X.presheaf.germ U (genericPoint X) hg).hom f = y)
    (ht : ∀ j, (X.presheaf.germ U (genericPoint X) hg).hom (t j) = algebraMap F X.functionField (x j.succ / x 0)) :
    Nonempty ((Γ(X, U) ⧸ Ideal.span (Set.range t)) ≃+*
      (rB ℂ X.functionField x {0} ⧸ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) := by
  set g := (X.presheaf.germ U (genericPoint X) hg).hom
  have hinj : Function.Injective g := germ_injective_of_isIntegral X _ hg
  let g' : Γ(X, U) →+* rB ℂ X.functionField x {0} :=
    g.codRestrict (rB ℂ X.functionField x {0}).toSubring fun f => (hring _).2 ⟨f, rfl⟩
  have hbij : Function.Bijective g' := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (hring y).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  let e := RingEquiv.ofBijective g' hbij
  refine ⟨Ideal.quotientEquiv _ _ e ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact Subtype.ext (ht j).symm

theorem exists_finCover_fibre_reduced : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  intro X _ p d _ inst hinst hproj S
  obtain ⟨N, ι, hι, hιp⟩ := hproj
  obtain ⟨n, f, hf, hn, hcov, hgen, hS, htr⟩ := GlobalTheory.T.exists_forms_transversal_at_complexPoints X p d N ι hι hιp S
  obtain ⟨F, x, hFC, hAC, hx⟩ := GlobalTheory.T.exists_finiteCover_affineCover_of_forms_no_commonZero X p d hinst N ι hι hιp n f hf hn hcov hgen
  set U0 := GlobalTheory.EtProj.fOpen ι (f 0) with hU0
  set t : Fin d → Γ(X, U0) := fun j => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0) with ht_def
  have hx0 : x 0 = 1 := by
    apply (algebraMap F X.functionField).injective
    rw [hx 0, GlobalTheory.EtProj.fRatio_self, map_one, map_one]
  have ht : ∀ j, (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom (t j) =
      algebraMap F X.functionField (x j.succ / x 0) := by
    intro j
    rw [hx0, div_one, hx j.succ]
  have hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔
      ∃ g : Γ(X, U0), (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom g = y := by
    intro y
    have hle : ({0} : Finset (Fin (d + 1))).inf (fun i => GlobalTheory.EtProj.fOpen ι (f i)) = U0 := by simp [hU0]
    rw [hAC.ring {0} (Finset.singleton_nonempty 0) y]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.ge).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.ge) _ _ g
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.le).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.le) _ _ g
  obtain ⟨E⟩ := quotEquiv_of_germ x U0 (hgen 0) t hring ht
  have hU0aff : IsAffineOpen U0 := by
    simpa [hU0] using hAC.affine {0} (Finset.singleton_nonempty 0)
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI hart : IsArtinianRing (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    haveI := GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover ℂ X.functionField F d x hFC
    exact RingEquiv.isArtinianRing E.symm
  have hred : IsReduced (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    refine GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' _ _ hart fun m hm hIm => ?_
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal X p U0 hU0aff m hm
    refine htr y hy fun j => ?_
    exact hIm (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨F, x, fun i => GlobalTheory.EtProj.fOpen ι (f i), hFC, hAC, ?_, fun y hyS => ⟨(hS y hyS).1, ?_⟩⟩
  · haveI := hred
    exact isReduced_of_injective E.symm E.symm.injective
  · intro j hg g hgj
    have : g = t j := by
      apply germ_injective_of_isIntegral X _ hg
      exact hgj.trans (ht j).symm
    rw [this]
    exact (hS y hyS).2 j

end GlobalTheory.PD.FibRed
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteCoverProjSpaceReducedFibreOriginStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential
theorem _root_.GlobalTheory.T.exists_finiteCover_projSpace_reduced_fibre_origin : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  first | exact @GlobalTheory.PD.FibRed.exists_finCover_fibre_reduced | exact GlobalTheory.PD.FibRed.exists_finCover_fibre_reduced | exact @GlobalTheory.PD.FibRed.quotEquiv_of_germ | exact GlobalTheory.PD.FibRed.quotEquiv_of_germ
end
end
