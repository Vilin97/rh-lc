module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiOfClosedTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ColInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoordWD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoreUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoverJ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.DvdMulEntriesRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FixOfHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumpsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTowerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBoundsStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FuncHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvQHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkRec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.OpExHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.OpOneHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowDvdOfEv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowTrHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.SecUHolds
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TieRep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLimHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLinHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TraceEqNextCoeff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.WeilPhi
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ZeroAp

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FixWHolds

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixW_holds :
    FixW := by
  intro l _ K bk P AI T n hn s
  set x := f0 bk s with hx
  have hact := ActLaws.act_laws l
  have hσB : ∀ (g : GQ l) (y : Per.Acris l), Per.σB g (iB l y) = iB l (sigA g y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.1
  have hφB : ∀ y : Per.Acris l, Per.φB l (iB l y) = iB l (phiA l y) :=
    hact.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hfix : ∀ g : ↥(GK K), sigA (g : GQ l) x = x := by
    intro g
    have hxe : x = iA l (WittVector.frobenius (bk.ev (PowerSeries.C (PowerSeries.constantCoeff s)))) := by
      simp only [hx, f0, fA, RingHom.comp_apply, bk.ev_frob]
    rw [hxe, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g]
  have hinj : Function.Injective (iB l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
  set b := T.eB.symm (iB l x) with hb
  have hbfix : ∀ g : ↥(GK K), (P.PD K).actB g b = b := by
    intro g
    apply T.eB.injective
    rw [P.PD_actB, T.actB, hb, RingEquiv.apply_symm_apply, hσB, hfix]
  obtain ⟨c, hc⟩ := (P.PD K).invB b hbfix
  have hc' : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ = b := hc
  have hit : ∀ (m : ℕ) (y : ↥(MaximalUnramifiedExtension l)), (fun z => P.φB z)^[m] (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B y) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((frobUr l ^ m) y) := by
    intro m y
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, phiB_algebraMap, pow_succ', AlgHom.mul_apply]
  have hbn : (fun z => P.φB z)^[n] b = b := by
    rw [← hc', hit, hn ⟨c, c.2.2⟩ c.2.1]
  have htr : ∀ (m : ℕ) (y : P.R.B), T.eB ((fun z => P.φB z)^[m] y) = (Per.φB l)^[m] (T.eB y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', T.frob, ih]
  have hin : ∀ (m : ℕ) (y : Per.Acris l), (Per.φB l)^[m] (iB l y) = iB l ((phiA l)^[m] y) := by
    intro m y
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hφB]
  apply hinj
  have h1 := htr n b
  rw [hbn, hb, RingEquiv.apply_symm_apply, hin] at h1
  rw [RingHom.coe_pow]
  exact h1.symm
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FrExHolds

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.frEx_holds :
    FrEx := by
  intro l _ K L₀ bk τp hτp P AI T a hL₀ r Cl Cv J hCl hcr
  haveI := K.2
  let N : ℕ := Finset.univ.sup fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup
  have hN : ∀ τ', ∀ n ∈ J τ', |n| ≤ (N : ℤ) := by
    intro τ' n hn
    rw [Int.abs_eq_natAbs]
    have h1 : n.natAbs ≤ ((J τ').map Int.natAbs).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ').map Int.natAbs).sup ≤ N :=
      Finset.le_sup (f := fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup) (Finset.mem_univ τ')
    exact_mod_cast h1.trans h2
  have hsstCl : ∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R :=
    fun ρ₁ h L r' R h1 h2 h3 => (hCl ρ₁ h L r' R h1 h2 h3).1
  have hsst : ∀ m, IsSst P (qRep (Cv.tw.ρ' m)) := fun m =>
    (GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).1 hsstCl
  have hfr : ∀ m, ∃ F : Frame bk N (Cv.tw.d' m) (fun g => (Cv.tw.ρ' m g).val),
      F.IsDR ∧ (IsCrys (P.PD K) (qRep (Cv.tw.ρ' m)) → F.IsCr) := fun m =>
    GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps l K bk τp hτp P AI T N _ (Cv.tw.ρ' m) (Cv.cont' m) (hsst m)
      (GlobalTheory.T.layer_DdR_bounds_alt l K L₀ P AI T a Cl J N hL₀ hN _ (Cv.tw.ρ' m) (Cv.lay m) hCl)
  choose F hFdr hFcr using hfr
  obtain ⟨F₀, -, hF₀cr, rr, hlink⟩ := GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower l K bk τp hτp Cv.d N Cv.ρ Cv.tw F hFdr
  have hFc : ∀ m, (F m).IsCr := fun m =>
    hFcr m ((GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).2 hcr)
  exact ⟨N, F, F₀, rr, hFc, hF₀cr hFc, hlink⟩
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkOp

section

@[expose] public section

noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem linkOp_holds : LinkOp2 := by
  intro R _ π s d d' W Z Zs W₁ Z₁ Zs₁ Pm R₀ h1 h2 hA hB i j
  have hl : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) R) (A : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (X * A) i j := by
    intro m n p X A h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h k j).mul_left _
  have hr : ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) R) (Y : Matrix (Fin n) (Fin p) R),
      (∀ i j, π ∣ A i j) → ∀ i j, π ∣ (A * Y) i j := by
    intro m n p A Y h i j
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun k _ => (h i k).mul_right _
  have e1 : W * Zs * Pm * Z₁ * Zs₁ = s • (W * Zs * Pm) := by
    rw [Matrix.mul_assoc (W * Zs * Pm), h2, Matrix.mul_smul, Matrix.mul_one]
  have e2 : W * Zs * Z * R₀ * Zs₁ = s • (W * R₀ * Zs₁) := by
    rw [Matrix.mul_assoc W Zs Z, h1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.smul_mul]
  have key : s • (W * Zs) * Pm - Pm * s • (W₁ * Zs₁) =
      W * Zs * (Pm * Z₁ - Z * R₀) * Zs₁ - s • ((Pm * W₁ - W * R₀) * Zs₁) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, smul_sub, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [e1, e2]
    abel
  rw [key, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_sub (hr _ _ (hl _ _ hA) i j) ((hr _ _ hB i j).mul_left s)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkZHolds

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkZ_holds :
    LinkA → LinkQ → LinkZ := by
  intro hA hQ l _ K bk τ hτ N M
  obtain ⟨n, hn⟩ := hQ l K bk N M
  refine ⟨max n M, ?_⟩
  intro k d d' ρ ρ' F F' Y Y₁ hY hY₁ Q Q' Q₁ Q₁' hS hS₁ Pi R hL
  obtain ⟨h1, h2⟩ := hA l K bk τ hτ N d d' (max n M) ρ ρ' F F' Y Y₁ hY hY₁ Pi R hL
  have hfz : ∀ z : ℤ_[l], fI l (Per.zA l z) = zC l z := fun z => by
    have h := (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z
    simp only [fI, zC, RingHom.comp_apply]
    rw [← GlobalTheory.RingBasics.φA_apply, h]
  have hfe : ∀ s : bk.S, fI l (bk.ev s) = fA bk s := fun s => by
    simp only [fI, fA, RingHom.comp_apply, bk.ev_frob]
  have hlM : ∀ i j, (l : Per.Acris l) ^ M ∣
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) i j := by
    intro i j
    have h := map_dvd (fI l) (h1 i j)

    simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hfz, hfe,
    map_pow, map_natCast] at h ⊢
    exact (pow_dvd_pow _ (le_max_right _ _)).trans h
  have h3 := hn k d d' F.A F'.A F'.A' Q Q' Q₁ Q₁' R F'.A_mul hS hS₁
    (fun i j => (pow_dvd_pow _ (le_max_left _ _)).trans (h2 i j))
  intro i j
  have e : Pi.map (zC l) * (Y₁.map (fI l) * Q₁) - (Y.map (fI l) * Q) * R.map (f0 bk) =
      (Pi.map (zC l) * Y₁.map (fI l) - Y.map (fI l) * R.map (fA bk)) * Q₁ +
        Y.map (fI l) * (R.map (fA bk) * Q₁ - Q * R.map (f0 bk)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact dvd_add (Finset.dvd_sum fun x _ => (hlM i x).mul_right _)
    (Finset.dvd_sum fun x _ => (h3 x j).mul_left _)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TestTr

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.testTr_holds :
    TestTr := by
  intro l _ P AI T d s v v₀ t p hv h lam
  subst hv
  let Λ : OB P →ₗ[↥(MaximalUnramifiedExtension l)] Bst P :=
    (TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P)).toLinearMap ∘ₗ lam.rTensor (Bst P)
  have hΛ : ∀ (x : Om l) (b : Bst P), Λ (x ⊗ₜ b) = lam x • b := by
    intro x b
    change TensorProduct.lid (↥(MaximalUnramifiedExtension l)) (Bst P) (lam.rTensor (Bst P) (x ⊗ₜ b)) = lam x • b
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
  have h1 := congrArg Λ h

  rw [map_sum, hΛ] at h1
  simp only [hΛ] at h1
  have hc : lam p • (1 : Bst P) = Polynomial.C (lam p • (1 : P.R.B)) := by
    rw [← Polynomial.smul_C, map_one]
  have h2 : (∑ i, lam (t i) • T.eB.symm (v₀ i)) = lam p • (1 : P.R.B) := by
    apply Polynomial.C_injective

    rw [map_sum, ← hc, ← h1]
    simp only [Polynomial.smul_C]
  simp only [Algebra.smul_def] at h2
  have h3 := congrArg T.eB h2

  simp only [map_sum, map_mul, map_one, mul_one, RingEquiv.apply_symm_apply] at h3
  have h4 : ∑ i, uB T (lam (t i)) * v₀ i = uB T (lam p) := h3
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrIdHolds

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trId_holds :
    TrId := by
  intro l _ B _ u zb hz s d d' m t t' c pv p θ Pi e e' V V' h1 h2 lam
  have hscal : ∀ (z : ℤ_[l]) (x : Om l), u (lam (zOm l z * x)) = zb z * u (lam x) := by
    intro z x
    have hx : zOm l z * x = (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) • x := by
      rw [Algebra.smul_def]
      rfl
    rw [hx, map_smul, smul_eq_mul, map_mul, hz]
  have hk : ∀ k, ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (c k * t' j k)) = s * u (lam (c k * pv k)) := by
    intro k
    simpa using h2 k (lam ∘ₗ LinearMap.mulLeft ↥(MaximalUnramifiedExtension l) (c k))
  have hE : (fun i => zb ((Pi *ᵥ e' - e) i)) = Pi.map zb *ᵥ (fun j => zb (e' j)) - fun i => zb (e i) := by
    funext i

    simp [Matrix.mulVec, dotProduct, map_sum]
  have hX : (V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ (fun i => zb ((Pi *ᵥ e' - e) i)) =
      V *ᵥ (fun i => zb (e i)) - Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j)) := by
    rw [hE, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    abel
  have hA := h1 lam
  have hS1 : ∑ i, ((V * Pi.map zb - Pi.map zb * V') *ᵥ (fun j => zb (e' j)) - V *ᵥ fun i => zb ((Pi *ᵥ e' - e) i)) i * u (lam (t i)) =
      s * u (lam p) - ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
    rw [hX, ← hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [_root_.Pi.sub_apply]
    ring
  have hS2 : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * u (lam (∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k)) =
      ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) - ∑ k, s * u (lam (c k * pv k)) := by
    have ha : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ i, zb (Pi i j) * u (lam (t i)) =
        ∑ i, (Pi.map zb *ᵥ (V' *ᵥ fun j => zb (e' j))) i * u (lam (t i)) := by
      generalize (V' *ᵥ fun i => zb (e' i)) = w
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hb : ∑ j, (V' *ᵥ fun i => zb (e' i)) j * ∑ k, u (lam (c k * t' j k)) = ∑ k, s * u (lam (c k * pv k)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => hk k
    rw [← ha, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_

    simp only [map_sub, map_sum, hscal, mul_sub]
  have hS3 : s * u (lam (θ - ∑ k, c k * pv k)) = s * u (lam θ) - ∑ k, s * u (lam (c k * pv k)) := by

    simp only [map_sub, map_sum, mul_sub, Finset.mul_sum]
  rw [hS1, hS2, hS3, map_sub, map_sub, mul_sub]
  ring
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiHolds

section

@[expose] public section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem ClosedTr_holds : ClosedTr :=
  closedTr_of coverJ_holds frEx_holds
    (opEx_holds (secU_holds coreU_holds) invQ_holds invU_holds (linkZ_holds linkA_holds (linkQ_holds zeroAp_holds linkRec_holds))
      linkOp_holds fixW_holds opOne_holds)
    fixOf_holds
    (tie_holds (tieRep_holds trLin_holds coordEx_holds coordWD_holds colInv_holds weilPhi_holds testTr_holds))
    (trLim_holds (trStep_holds (func_holds intBasis_holds) trId_holds))

theorem congPhi_holds : GlobalTheory.CongPhi.ClosedPhi := congPhi_of_closedTr ClosedTr_holds powTr_holds

end UpperTheory.Gal.ClosedPhiFromClosedTrace
end
end
