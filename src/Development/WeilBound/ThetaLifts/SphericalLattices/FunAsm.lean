module

public import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Inertof
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Kcompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsInvariantForm
public import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlBridge
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.LocalThetaKernels.EvlLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.WeilBound.CoreStatements.LocalThetaKernels.EvlDual

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}


open scoped nonZeroDivisors in
theorem exists_dual_frame {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (L : Submodule R V) [Module.Finite R L]
    (hden : ∀ z : V, ∃ a : R, a ≠ 0 ∧ a • z ∈ L) :
    ∃ (N : ℕ) (e : Fin N → V) (g : Fin N → V →ₗ[K] K), (∀ i, e i ∈ L) ∧
      (∀ i, ∀ x ∈ L, ∃ a : R, g i x = algebraMap R K a) ∧ ∀ x, ∑ i, g i x • e i = x := by
  classical
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have canc : ∀ a : R, a ≠ 0 → ∀ x y : V, a • x = a • y → x = y := fun a ha x y h => by
    rw [← algebraMap_smul K, ← algebraMap_smul K a y] at h
    exact smul_right_injective V ((map_ne_zero_iff _ inj).2 ha) h
  have : Module.IsTorsionFree R L := by
    refine ⟨fun a ha x y h => Subtype.ext (canc a ha.ne_zero _ _ (congrArg Subtype.val h))⟩
  have : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨N, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R L
  have : IsLocalizedModule R⁰ L.subtype :=
    { map_units := fun a => by
        rw [← (Algebra.lsmul R (A := K) R V).commutes]
        exact (IsLocalization.map_units K a).map _
      surj := fun y => by
        obtain ⟨a, ha, h⟩ := hden y
        exact ⟨(⟨_, h⟩, ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have hb := IsLocalizedModule.isBaseChange R⁰ K L.subtype
  let G : Fin N → V →ₗ[K] K := fun i => hb.lift (Algebra.linearMap R K ∘ₗ LinearMap.proj i ∘ₗ g)
  have hG : ∀ i (x : L), G i x = algebraMap R K (g x i) := fun i x => hb.lift_eq _ x
  refine ⟨N, fun i => f (Pi.single i 1), G, fun i => (f _).2, fun i x hx => ⟨_, hG i ⟨x, hx⟩⟩, fun x => ?_⟩
  obtain ⟨a, ha, h⟩ := hden x
  refine canc a ha _ _ ?_
  have h1 : f (g ⟨_, h⟩) = ⟨_, h⟩ := LinearMap.congr_fun hfg _

  rw [← Finset.univ_sum_single (g ⟨_, h⟩), map_sum] at h1
  have h2 := congrArg Subtype.val h1
  rw [Submodule.coe_sum] at h2
  rw [Finset.smul_sum]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
  have e1 : (Pi.single i (g ⟨_, h⟩ i) : Fin N → R) = g ⟨_, h⟩ i • (Pi.single i 1 : Fin N → R) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e1, map_smul, Submodule.coe_smul, ← algebraMap_smul K (g ⟨_, h⟩ i), ← hG, ← smul_assoc, LinearMap.map_smul_of_tower]

omit [NumberField F] [NumberField E] in
theorem exists_form {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (c : Fin n → E) :
    ∃ x', ∀ x, form σ J x' x = ∑ i, c i * σ (x i) := by
  refine ⟨c ᵥ* J⁻¹, fun x => ?_⟩
  rw [form, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ.isUnit, Matrix.vecMul_one]
  rfl

omit [NumberField F] [NumberField E] in
theorem form_smul (J : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) : form σ J x (a • y) = σ a * form σ J x y := by
  simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm]

omit [NumberField F] [NumberField E] in
theorem rep_E {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) :
    ∃ x', ∀ x, form σ J x' x = σ (g x) := by
  obtain ⟨x', h⟩ := exists_form (σ := σ) hJ fun i => σ (g fun j => if i = j then 1 else 0)
  refine ⟨x', fun x => ?_⟩

  rw [h, g.pi_apply_eq_sum_univ x, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, map_mul, mul_comm]

theorem rep_F (hσ : ∀ z, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[F] F) :
    ∃ x', ∀ x, Algebra.trace F E (form σ J x' x) = g x := by
  have hn := traceForm_nondegenerate F E
  obtain ⟨x', h⟩ := exists_form (σ := σ) hJ fun i =>
    ((Algebra.traceForm F E).toDual hn).symm (g ∘ₗ LinearMap.single F (fun _ => E) i ∘ₗ σ.toLinearMap)
  refine ⟨x', fun x => ?_⟩

  rw [h, map_sum]

  conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  simp [hσ]

theorem invol (h : IsCMExt F E σ) (z : E) : σ (σ z) = z := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem isIntegral_map {z : E} (h : IsIntegral ℤ z) : IsIntegral ℤ (σ z) := h.map (σ.toRingHom.toIntAlgHom)

theorem frame_X {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) :
    ∃ (N : ℕ) (x x' : Fin N → Fin n → E), (∀ i, x i ∈ X.L) ∧ (∀ i, x' i ∈ X.L) ∧
      ∃ g : Fin N → (Fin n → E) → E, (∀ i z, form σ X.J (x' i) z = σ (g i z)) ∧ ∀ z, ∑ i, g i z • x i = z := by
  have hJ : X.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hX.sig w) ?_
    rw [show (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det from (RingHom.map_det _ _).symm, h0, map_zero]
  have : Module.Finite (𝓞 E) X.L := Module.Finite.iff_fg.mpr hX.lat.fg
  obtain ⟨N, e, g, he, hg, hs⟩ := exists_dual_frame (K := E) X.L fun z => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.LatOpenCpt.exists_zsmul_mem X.L hX.lat z
    exact ⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose x' hx' using fun i => rep_E (σ := σ) hJ (g i)
  refine ⟨N, e, x', he, fun i => (hX.dual _).2 fun x hx => ?_, fun i z => g i z, hx', hs⟩
  obtain ⟨a, ha⟩ := hg i x hx
  rw [hx', ha]
  exact isIntegral_map a.isIntegral_coe

theorem frame_alt_alt {B : Base F E} {W : Spc F E d} {r s : ℕ} (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) :
    ∃ (N : ℕ) (y y' : Fin N → Fin d → E), (∀ i, y i ∈ W.L) ∧ (∀ i, y' i ∈ W.L) ∧
      ∀ z, ∑ i, Algebra.trace F E (form σ W.J (y' i) z) • y i = z := by
  have hσ := invol hB.cm
  have hJ : W.J.det ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    refine GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hW.sig w) ?_
    rw [Matrix.det_smul, show (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det from (RingHom.map_det _ _).symm, h0,
      map_zero, mul_zero]
  have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.mpr hW.lat.fg
  have : Module.Finite (𝓞 F) W.L := Module.Finite.trans (𝓞 E) W.L
  have : Module.Finite (𝓞 F) (W.L.restrictScalars (𝓞 F)) := this
  obtain ⟨N, e, g, he, hg, hs⟩ := exists_dual_frame (K := F) (W.L.restrictScalars (𝓞 F)) fun z => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.LatOpenCpt.exists_zsmul_mem W.L hW.lat z
    exact ⟨m, Int.cast_ne_zero.2 hm, by rwa [Int.cast_smul_eq_zsmul]⟩
  choose y' hy' using fun i => rep_F hσ hJ (g i)
  refine ⟨N, e, y', he, fun i => (hW.dual _).2 fun x hx o => ?_, fun z => by simpa only [hy'] using hs z⟩
  let o' : 𝓞 E := ⟨σ o, isIntegral_map o.isIntegral_coe⟩
  obtain ⟨a, ha⟩ := hg i (o' • x) (W.L.smul_mem o' hx)
  have e1 : (o : E) * form σ W.J (y' i) x = form σ W.J (y' i) (o' • x) := by
    rw [show o' • x = σ (o : E) • x from rfl, form_smul, hσ]
  rw [e1, ← Algebra.trace_trace (S := F), hy', ha]
  exact Algebra.isIntegral_trace a.isIntegral_coe

theorem exists_frames {B : Base F E} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    ∃ (ι : Type) (_ : Fintype ι) (x x' : ι → Fin n → E) (y y' : ι → Fin d → E),
      (∀ i, x i ∈ X.L ∧ x' i ∈ X.L ∧ y i ∈ W.L ∧ y' i ∈ W.L) ∧ ∀ u : Matrix (Fin n) (Fin d) (AE F E),
        u = ∑ i, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F (Matrix.vecMulVec (x' i) (y' i))) u •
          incM F (Matrix.vecMulVec (x i) (y i)) := by
  obtain ⟨N, x, x', hx, hx', g, hg, hgs⟩ := frame_X hX
  obtain ⟨N', y, y', hy, hy', hs⟩ := frame_alt_alt hB hW
  refine ⟨Fin N × Fin N', inferInstance, fun p => x p.1, fun p => -x' p.1, fun p => y p.2, fun p => y' p.2,
    fun p => ⟨hx _, neg_mem (hx' _), hy _, hy' _⟩, fun u => ?_⟩
  have hu := GlobalTheory.LatOpenCpt.span_top (F := F) hX.lat hW.lat (fun p : X.L × W.L => Matrix.vecMulVec p.1.1 p.2.1)
    (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩) u
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩ := hz
    have key : Matrix.vecMulVec a b = ∑ p : Fin N × Fin N',
        Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b)) • Matrix.vecMulVec (x p.1) (y p.2) := by
      rw [Fintype.sum_prod_type]
      conv_lhs => rw [← hgs a]
      ext i j
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Finset.sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := congrFun (hs (g k a • b)) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      rw [mul_comm (g k a), mul_assoc, ← h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_smul_comm]
    have hs' : ∀ p : Fin N × Fin N', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
        (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) (incM F (Matrix.vecMulVec a b)) =
        algebraMap F (AF F) (Algebra.trace F E (form σ W.J (y' p.2) (g p.1 a • b))) := fun p => by
      have h := GlobalTheory.LatVacArith.symp_incM σ X.J W.J (-1) (-x' p.1) a (y' p.2) b
      rw [map_neg, map_one] at h
      rw [h, form_smul, ← hg]
      simp [form]
    simp only [hs']
    conv_lhs => rw [key]
    ext i j

    simp only [incM, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, algebraMap_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
  | zero => simp [GlobalTheory.LatVacArith.symp_zero_right]
  | add a b _ _ ha hb =>
    simp only [GlobalTheory.LatVacArith.symp_add_right, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb]
  | smul a z _ hz =>
    conv_lhs => rw [hz, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 a
      (incM F (Matrix.vecMulVec (-x' p.1) (y' p.2))) z
    rw [one_smul, one_mul] at h
    rw [h, smul_smul]

theorem mem_latAtV_of_dual {B : Base F E} {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {v : Pl F} (hv : PsiUnr B.ψ v)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ u) = 1) :
    u ∈ latAtV X W v := by
  obtain ⟨ι, _, x, x', y, y', hm, he⟩ := exists_frames hB hX hW
  rw [he u]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have hat : At (evFin F v) (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (incM F (Matrix.vecMulVec (x' i) (y' i))) u) := fun t ht => by
    have h := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 t (incM F (Matrix.vecMulVec (x' i) (y' i))) u
    rw [hu t ht, GlobalTheory.LatVacArith.symp_zero_right, one_mul] at h
    exact h.symm
  refine AddSubgroup.subset_closure ⟨_, hat, (hv _).1 fun a ha => ?_, _, (hm i).1, _, (hm i).2.2.1, rfl⟩
  have h1 := h _ (AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, _, (hm i).2.1, _, (hm i).2.2.2, rfl⟩)
  have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) (GlobalTheory.LatVac.liftV v a) 1
    (incM F (Matrix.vecMulVec (x' i) (y' i))) u
  rw [one_smul, mul_one] at h2
  have hat' : At (evFin F v) (GlobalTheory.LatVac.liftV v a *
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
        (incM F (Matrix.vecMulVec (x' i) (y' i))) u) := fun t ht => by
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul t _, hat t ht, mul_zero]
  rw [h2, GlobalTheory.StdVacuum.psi_eq_psiLoc _ v _ hat', map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
  exact h1

end PositivityTheory.ThKH.Evl
end
end
end

-- Source module: Development.WeilBound.CoreStatements.LocalThetaKernels.EvlMain

section

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKH.Evl

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.LatVac (liftV psiAt locCo evFin_liftV at_liftV)
open PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem psiAt_good {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (v : Pl F) :
    Continuous (psiAt ψ v) ∧ (∀ x, ‖psiAt ψ v x‖ = 1) ∧ psiAt ψ v ≠ 1 :=
  ⟨GlobalTheory.VacAny.continuous_psiV h.1 v, fun _ => GlobalTheory.StdCharFromIsStd.norm_psi h _, GlobalTheory.PsiNontriv.psiAt_ne_one ψ h v⟩

theorem evVac : PositivityTheory.ThK.EvVac := by
  rintro F E _ _ _ _ _ σ n d B X W M om hP v ⟨w₀, hw₀⟩ m Cy hL ⟨Cx, hLx, hsp⟩
  obtain ⟨hc, hn, h1⟩ := psiAt_good hP.base.std v
  obtain ⟨r, s, hX⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  obtain ⟨l, ⟨φ, hφ, hlφ⟩, hl⟩ := GlobalTheory.CompanionTheory.LagFun.exists_invariant_form (Fv F v) (Fin n × Fin d) (psiAt B.ψ v) hc h1
    (lagr M v Cy) (lagr_iso M hL)
  refine ⟨l, (isEvAt_iff M hL B.ψ l).2 hl, fun h0 => hlφ ?_⟩
  obtain ⟨hS, hne, θ, -, hvac⟩ := hP.good.vac v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  refine core hc hn h1 hS hne (lagr M v Cy) l hl (fun w => ?_) h0 φ hφ
  obtain ⟨u, rfl⟩ := exists_locCo M.co w
  obtain ⟨z, z', e⟩ := space_split hX.lat hW.lat hsp u
  refine ⟨_, ⟨z, rfl⟩, locCo M.co v (z' * Cxᵀ), by rw [e, map_add (f := _)], ?_⟩
  by_cases hz : z' * Cxᵀ ∈ latAtV X W v
  · exact Or.inl ⟨_, ((acts_iff M.co B.ψ (hat _ hz) hS).1 (hvac _ hz)).symm⟩
  · right
    by_contra hcon
    refine hz (mem_latAtV_of_dual hP.base hX hW (hP.base.inert v w₀ hw₀).2.2 (at_mul hLx.supp z') fun γ hγ => ?_)
    obtain ⟨y, y', hy, rfl⟩ := lat_split hsp hγ
    rw [GlobalTheory.LatVacArith.symp_add_left, symp_lag hLx, add_zero, psi_form M.co B.ψ (hat _ hy)]
    by_contra hne'
    refine hcon ⟨_, ⟨y, rfl⟩, ?_, hne'⟩
    have h := (acts_iff M.co B.ψ (hat _ hy) hS).1 (hvac _ hy)
    rw [symp_lag hL, mul_zero, AddChar.map_zero_eq_one, one_smul] at h
    exact h.symm

end PositivityTheory.ThKH.Evl
end
end
end

-- Source module: Development.WeilBound.ThetaLifts.SphericalLattices.FunAsm

section

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

theorem relIndex_ne_zero_of_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K H : Subgroup G}
    (hK : IsCompact (K : Set G)) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) (hH : ∀ k ∈ K, k ∈ U → k ∈ H) : H.relIndex K ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) :=
    (H.subgroupOf K).isOpen_of_mem_nhds (Filter.mem_of_superset (continuous_subtype_val.continuousAt (x := (1 : K)) hU)
      fun k hk => Subgroup.mem_subgroupOf.2 (hH k.1 k.2 hk))
  have : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

section Form

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

def stabK (L : IsLocRep M ψ om v ω ρ) (φ : Fn F n d v) (hφ : φ ∈ SB _) : Subgroup (UA σ W.J) where
  carrier := {k | k ∈ KAt σ W v ∧ ω (1, k) φ = φ}
  one_mem' := ⟨(KSub σ W v).one_mem, L.one φ hφ⟩
  mul_mem' := fun {a b} ha hb => ⟨(KSub σ W v).mul_mem ha.1 hb.1, by rw [L.mulW ha.1.1 hb.1.1 hφ, hb.2, ha.2]⟩
  inv_mem' := fun {a} ha => ⟨(KSub σ W v).inv_mem ha.1, by
    have e := L.mulW (inv_mem_UAt ha.1.1) ha.1.1 hφ
    rw [inv_mul_cancel, ha.2] at e
    rw [← e]
    exact L.one φ hφ⟩

theorem exists_form (hAvg : AvgSt) (L : IsLocRep M ψ om v ω ρ) (hKc : IsCompact (KAt σ W v))
    (hfix : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) (hs : M.vac v ∈ SB _)
    (l₀ : Fn F n d v →ₗ[ℂ] ℂ) (h0 : l₀ (M.vac v) ≠ 0)
    (hX : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, l₀ (ω (g, 1) φ) = l₀ φ)
    (hfin : ∀ h ∈ UAt σ W (evFin F v), (conjInf (KSub σ W v) h).relIndex (KSub σ W v) ≠ 0) :
    ∃ l, IsSphForm M om v ω l ∧ ∀ h ∈ UAt σ W (evFin F v),
      l (ω (1, h) (M.vac v)) = avgK (KSub σ W v) (fun g => l₀ (ω (1, g) (M.vac v)) / l₀ (M.vac v)) h := by
  classical
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsTopologicalGroup (UA σ W.J) := inferInstance
  have o1 := one_mem_UAt (σ := σ) X v
  have oW := one_mem_UAt (σ := σ) W v
  have stabFin : ∀ φ (hφ : φ ∈ SB _), (stabK L φ hφ).relIndex (KSub σ W v) ≠ 0 := fun φ hφ => by
    obtain ⟨U, hU, hU'⟩ := L.smooth φ hφ
    exact relIndex_ne_zero_of_nhds hKc hU fun k hk hkU => ⟨hk, hU' k hkU hk.1⟩
  obtain ⟨lam, hinv, hfor⟩ := hAvg (UA σ W.J) (Fn F n d v) (KSub σ W v) (SB _) (fun g => ω (1, g)) l₀
    (fun k hk φ hφ => L.pres 1 o1 k hk.1 φ hφ) (fun φ hφ => L.one φ hφ) (fun k hk k' hk' φ hφ => L.mulW hk.1 hk'.1 hφ)
    (fun φ hφ => ⟨stabK L φ hφ, fun k hk => hk.1, stabFin φ hφ, fun k hk => hk.2⟩)
  have haug : ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, lam (ω (g, 1) φ) = lam φ := fun g hg φ hφ => by
    have hφ' := L.pres g hg 1 oW φ hφ
    have hHK : stabK L φ hφ ⊓ stabK L _ hφ' ≤ KSub σ W v := fun k hk => hk.1.1
    have hHf := Subgroup.relIndex_inf_ne_zero (stabFin φ hφ) (stabFin _ hφ')
    rw [hfor _ hφ' _ hHK hHf (fun k hk => hk.2.2), hfor _ hφ _ hHK hHf (fun k hk => hk.1.2)]
    congr 1
    refine finsum_congr fun q => ?_
    have hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v) := (Quotient.out q).2.1
    have e : ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) (ω (g, 1) φ) =
        ω (g, 1) (ω (1, ((Quotient.out q : KSub σ W v) : UA σ W.J)) φ) := by
      rw [← L.mul 1 o1 _ hk g hg 1 oW φ hφ, ← L.mul g hg 1 oW 1 o1 _ hk φ hφ, one_mul, mul_one, mul_one, one_mul]
    change l₀ (ω (1, _) (ω (g, 1) φ)) = l₀ (ω (1, _) φ)
    rw [e, hX g hg _ (L.pres 1 o1 _ hk φ hφ)]
  have hsub : Subsingleton (KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v)) :=
    ⟨fun x y => Quotient.inductionOn₂' x y fun a b => QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)⟩
  have hvac : lam (M.vac v) = l₀ (M.vac v) := by
    let q₀ : KSub σ W v ⧸ (KSub σ W v).subgroupOf (KSub σ W v) := QuotientGroup.mk 1
    rw [hfor _ hs (KSub σ W v) le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hfix, Subgroup.relIndex_self,
      Nat.cast_one, inv_one, one_mul, finsum_eq_single _ q₀ fun x hx => absurd (Subsingleton.elim x q₀) hx]
    exact congrArg l₀ (hfix _ (Quotient.out q₀).2)
  refine ⟨(l₀ (M.vac v))⁻¹ • lam, ⟨Submodule.span_le.2 ?_, fun k hk φ hφ => ?_, ?_⟩, fun h hh => ?_⟩
  · rintro _ ⟨g, hg, φ, hφ, φ₁, -, ha, rfl⟩
    rw [(L.acts g hg 1 oW φ hφ φ₁).1 ha]
    change (l₀ (M.vac v))⁻¹ • lam (ω (g, 1) φ - φ) = 0
    rw [map_sub, haug g hg φ hφ, sub_self, smul_zero]
  · change (l₀ (M.vac v))⁻¹ • lam (ω (1, k) φ) = (l₀ (M.vac v))⁻¹ • lam φ
    rw [hinv k hk φ hφ]
  · change (l₀ (M.vac v))⁻¹ • lam (M.vac v) = 1
    rw [hvac, smul_eq_mul, inv_mul_cancel₀ h0]
  · have hfixh : ∀ k ∈ conjInf (KSub σ W v) h, ω (1, k) (ω (1, h) (M.vac v)) = ω (1, h) (M.vac v) := fun k hk => by
      obtain ⟨k₁, hk₁, e⟩ := Subgroup.mem_map.1 hk.2
      have e' : k = h * k₁ * h⁻¹ := by rw [← e]; rfl
      rw [← L.mulW hk.1.1 hh hs, e', show h * k₁ * h⁻¹ * h = h * k₁ by group, L.mulW hh hk₁.1 hs, hfix k₁ hk₁]
    change (l₀ (M.vac v))⁻¹ • lam (ω (1, h) (M.vac v)) = _
    rw [hfor _ (L.pres 1 o1 h hh _ hs) _ inf_le_left (hfin h hh) hfixh, avgK, smul_eq_mul, mul_left_comm, mul_finsum]
    congr 1
    refine finsum_congr fun q => ?_
    have hk : ((Quotient.out q : KSub σ W v) : UA σ W.J) ∈ UAt σ W (evFin F v) := (Quotient.out q).2.1
    change (l₀ (M.vac v))⁻¹ * l₀ (ω (1, _) (ω (1, h) (M.vac v))) = _
    rw [← L.mulW hk hh hs, div_eq_inv_mul]
    rfl

theorem fn_mul (L : IsLocRep M ψ om v ω ρ) (hfix : ∀ k ∈ KAt σ W v, ω (1, k) (M.vac v) = M.vac v) (hs : M.vac v ∈ SB _)
    {l₀ : Fn F n d v →ₗ[ℂ] ℂ} {p : UA σ W.J} (hp : p ∈ UAt σ W (evFin F v)) {c : ℂ}
    (hc : ∀ φ ∈ SB _, l₀ (ω (1, p) φ) = c * l₀ φ) {g k : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) (hk : k ∈ KAt σ W v) :
    l₀ (ω (1, p * g * k) (M.vac v)) / l₀ (M.vac v) = c * (l₀ (ω (1, g) (M.vac v)) / l₀ (M.vac v)) := by
  rw [L.mulW (mul_mem_UAt hp hg) hk.1 hs, hfix k hk, L.mulW hp hg hs, hc _ (L.pres 1 (one_mem_UAt X v) g hg _ hs),
    mul_div_assoc]

omit [NumberField E] in
theorem fn_val {l₀ : Fn F n d v →ₗ[ℂ] ℂ} (hs : M.vac v ∈ SB _) (h0 : l₀ (M.vac v) ≠ 0) {p : UA σ W.J} {c : ℂ}
    (hc : ∀ φ ∈ SB _, l₀ (ω (1, p) φ) = c * l₀ φ) : l₀ (ω (1, p) (M.vac v)) / l₀ (M.vac v) = c := by
  rw [hc _ hs, mul_div_assoc, div_self h0, mul_one]

end Form

theorem sphFun_of (hCount : CountSt) (hAvg : AvgSt) (hPInv : PInvSt) (hLift : UnitLiftSt) (hChar : CharSt) (hEv : EvInvSt)
    (hSieg : SiegSt) (hMod : ModSt) (hCart : CartanSt) (hFin : FinSt) : SphFun := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v he ω ρ ω' ρ' L L' hK hK'
  haveI : LocallyCompactSpace (Fv F v) :=
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  obtain ⟨w, hw⟩ := inert_of_local F E σ B hT.base v he
  have hv : v ∉ X.T := fun h => he.false (B.τ ⟨v, hT.chars.sub h⟩)
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨m, Cy, hL, hAd, hIw, -⟩ := PositivityTheory.ThKH.Iwas.iwasawa F E σ _ _ B _ _ _ _ P v hT.geo.even ⟨w, hw⟩
  obtain ⟨l₀, hl, hl0⟩ := PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨l₀', hl', hl0'⟩ := PositivityTheory.ThKH.Evl.evVac F E σ _ _ B _ _ _ _ P' v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨hs, -, -⟩ := hT.geo.hM.vac v
  obtain ⟨hs', -, -⟩ := hT.geo.hM'.vac v
  have hKc : IsCompact (KAt σ G.W v) := stabiliser_compact F E σ _ _ B _ _ _ _ P v
  have hch := hChar F E σ B a a' G X om om' hT v w hw hv
  have hfin := hFin F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw
  have hX := hEv F E σ _ _ B _ _ _ _ _ _ P hT.weil v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self'])
    ω ρ L m Cy hL hAd l₀ hl ⟨_, hs, hl0⟩
  have hX' := hEv F E σ _ _ B _ _ _ _ _ _ P' hT.weil' v w hw (fun z hz => by rw [MonoidHom.div_apply, (hch z hz).2, div_self'])
    ω' ρ' L' m Cy hL hAd l₀' hl' ⟨_, hs', hl0'⟩
  obtain ⟨l, hlS, hlf⟩ := exists_form hAvg L hKc hK hs l₀ hl0 hX hfin
  obtain ⟨l', hlS', hlf'⟩ := exists_form hAvg L' hKc hK' hs' l₀' hl0' hX' hfin
  refine ⟨l, l', hlS, hlS', fun h hh => ?_⟩
  rw [hlf h hh, hlf' h hh]
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v

  have hval : ∀ p ∈ PSub σ G.W v Cy, ∃ (z : (AE F E)ˣ) (u : (Fv F v)ˣ),
      (∀ φ ∈ SB _, l₀ (ω (1, p) φ) = (X.β z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ) * l₀ φ) ∧
      (∀ φ ∈ SB _, l₀' (ω' (1, p) φ) = (X.α z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * l₀' φ) ∧
      X.α z * X.β z = 1 ∧
      ((((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v) : ℕ) : ℝ) =
        ((sbClass (Fv F v)).modu u : ℝ) ^ m *
          ((((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex (PSub σ G.W v Cy ⊓ KSub σ G.W v) : ℕ) : ℝ) :=
    fun p hp => by
      have hp0 := hp
      obtain ⟨⟨hpU, t, ht⟩, -⟩ := hp0
      obtain ⟨-, hu⟩ := hPInv F E σ _ G.W v w hw m Cy hL p hp.1
      obtain ⟨z, hz, hzc⟩ := hLift F E v (hu t ht).unit
      refine ⟨z, Units.map (Algebra.norm (Fv F v) : Ev E v →* Fv F v) (hu t ht).unit,
        hSieg F E σ _ _ B G.V G.W G.M om _ _ P hT.weil v w hw ω ρ L m Cy hL hAd l₀ hl p hpU t ht z hz hzc _ ?_,
        hSieg F E σ _ _ B G.V' G.W G.M' om' _ _ P' hT.weil' v w hw ω' ρ' L' m Cy hL hAd l₀' hl' p hpU t ht z hz hzc _ ?_,
        (hch z hz).1, hMod F E σ _ B G.W _ _ hT.base hT.geo.hW v w hw m Cy hL hAd p hp t ht _ ?_⟩
      all_goals simp [hzc]
  refine hCount (UA σ G.W.J) (PositivityTheory.ThKH.Iwas.USub σ G.W v) (KSub σ G.W v) (PSub σ G.W v Cy) _ _ (fun k hk => hk.1)
    (fun p hp => hp.1.1) (fun g hg => ?_) (fun g hg => hCart F E σ _ B G.W _ _ hT.base hT.geo.hW hT.geo.even v w hw g hg)
    (fun g hg => hfin g hg) ?_ ?_ (fun p hp g hg k hk => ?_) (fun p hp g hg k hk => ?_) (fun p hp => ?_) h hh
  · obtain ⟨p, hp, k, hk, e⟩ := hIw g hg
    exact ⟨p, ⟨hp, (hPInv F E σ _ G.W v w hw m Cy hL p hp).1⟩, k, hk, e⟩
  · show l₀ (ω 1 (G.M.vac v)) / _ = 1
    rw [L.one _ hs, div_self hl0]
  · show l₀' (ω' 1 (G.M'.vac v)) / _ = 1
    rw [L'.one _ hs', div_self hl0']
  · obtain ⟨z, u, h1, -, -, -⟩ := hval p hp
    rw [fn_mul L hK hs hp.1.1 h1 hg hk, fn_val hs hl0 h1]
  · obtain ⟨z, u, -, h2, -, -⟩ := hval p hp
    rw [fn_mul L' hK' hs' hp.1.1 h2 hg hk, fn_val hs' hl0' h2]
  · obtain ⟨z, u, h1, h2, h3, h4⟩ := hval p hp
    rw [fn_val hs hl0 h1, fn_val hs' hl0' h2]
    have h3' : (X.α z : ℂ) * (X.β z : ℂ) = 1 := by rw [← Circle.coe_mul, h3, Circle.coe_one]
    have hR0 : 0 ≤ ((sbClass (Fv F v)).modu u : ℝ) := NNReal.coe_nonneg _
    have hm : (a : ℝ) / 2 + (a' : ℝ) / 2 = (m : ℝ) := by
      have : ((a : ℝ) + a') = 2 * m := by exact_mod_cast hL.rank
      linarith
    generalize ((sbClass (Fv F v)).modu u : ℝ) = R at hR0 h4 ⊢
    generalize (((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p).toMonoidHom).relIndex
      (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₁ at h4 ⊢
    generalize (((PSub σ G.W v Cy ⊓ KSub σ G.W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex
      (PSub σ G.W v Cy ⊓ KSub σ G.W v)) = n₂ at h4 ⊢
    have e : R ^ ((a : ℝ) / 2) * R ^ ((a' : ℝ) / 2) = R ^ m := by
      rw [← Real.rpow_add_of_nonneg hR0 (by positivity) (by positivity), hm, Real.rpow_natCast]
    have h4' : ((n₂ : ℕ) : ℂ) = ((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ) := by
      rw [← Complex.ofReal_mul, e]
      exact_mod_cast h4
    rw [h4']
    linear_combination (((R ^ ((a : ℝ) / 2) : ℝ) : ℂ) * ((R ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((n₁ : ℕ) : ℂ)) * h3'

end PositivityTheory.Sph

end
end
end
