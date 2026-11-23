module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesOfPrecomplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedTensorWittCompletePiAdicModEll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLattic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtalePhiMatrixDecompletionToWach

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl GlobalTheory.FrobDescent

noncomputable section

namespace GlobalTheory.HWL.MatDecompl

section Concrete

open GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
  {LL : FinExt l} {Γ : GamS P K s LL} {R : WSer Γ}

theorem res_eq_one (Γ : GamS P K s LL) (g : ↥(GK K)) (h1 : P.χQ (g : GQ l) = 1) :
    Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply Subtype.ext
  have := Γ.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at this
  exact this

theorem chi_eq_one (P : LocPrime l) (h : Good K s LL) {g : GQ l} (hg : g ∈ Hinf K) :
    P.χQ g = 1 :=
  ((cyc_basic l P.χQ P.χQ_cyc).2.2 K g
    (IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) (Hinf_le_GK h hg))).2.1 hg

theorem fixH_io (I : IoS AI R) (e : R.EE) : FixH AI K (I.ioE e) :=
  fun g hg h1 => io_fixed I ⟨g, hg⟩ (res_eq_one Γ ⟨g, hg⟩ h1) e

theorem fixH_pi (I : IoS AI R) : FixH AI K (piR AI LL s) := by
  have h := fixH_io I (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) R.EE letπ)
  set_option synthInstance.maxHeartbeats 400000 in
    rw [io_pi I] at h
  exact h

theorem exists_pole_RW (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (x : RW LL) :
    ∃ k, NearPi AI LL s 0 (piR AI LL s ^ k * x) := by
  choose k hk using fun i => exists_pow_mul AI s ((crd (basisO LL) i x).coeff 0)
  refine ⟨Finset.univ.sup k, (nearPi_iff_crd AI LL s _ _).2 fun i => ?_⟩
  obtain ⟨z, hz⟩ := hk i _ (Finset.le_sup (f := k) (Finset.mem_univ i))
  exact ⟨z, by rw [crd_piR_pow, hz, pow_zero, one_mul]⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_near_perfI (h : Good K s LL) (I : IoS AI R) (hI : IoW I) (x : RW LL)
    (hx : FixH AI K x) (m : ℕ) : ∃ u ∈ perfI I l, NearPi AI LL s m (x - u) := by
  obtain ⟨u, hu, hu'⟩ := exists_inv_perfI I l
  refine exists_near AI K LL s _ (algebraMap_mem_perfI I l) u hu hu' (lift_closure _ _ ?_)
    (fun g hg => fixH_pi I g (Hinf_le_GK h hg) (chi_eq_one P h hg))
    x (fun g hg => hx g (Hinf_le_GK h hg) (chi_eq_one P h hg)) m
  rintro y (⟨j, rfl⟩ | ⟨z, hz, k, hk, hl, hzk, hy⟩)
  · refine mem_perfI_of_iterate I l j (l ^ s) _ ?_
    refine (GlobalTheory.TorsionBoundCompare.tmul_iter LL j _).trans ?_
    rw [frob_iter_teich, εroot_pow]
    exact piR_add_one_pow AI LL s
  · have hint : ∀ i, Γ.emb i ⟨z, hz⟩ ∈ OL LL := fun i => by
      refine IsIntegral.of_pow hk ?_
      have : (⟨z, hz⟩ : ↥(K0 K)) ^ k = 1 := Subtype.ext hzk
      rw [← map_pow, this, map_one]
      exact isIntegral_one
    exact mem_perfI_of_io I l (hI ⟨z, hz⟩ k hk hl hzk y hy (fun i => ⟨_, hint i⟩) fun _ => rfl)

theorem mem_fixSub_iff (AI : LocAinf l P) (K : FinExt l) (x : RW LL) :
    x ∈ fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1} ↔ FixH AI K x :=
  mem_fixSub.trans ⟨fun h g h1 h2 => h g ⟨h1, h2⟩, fun h g hg => h g hg.1 hg.2⟩

theorem isUnit_one_add_RW (LL : FinExt l) (x : RW LL) : IsUnit (1 + (l : RW LL) * x) :=
  haveI := (GlobalTheory.HWL.TensorWitt.main l LL).1
  isUnit_one_add x

end Concrete

theorem conj_io' {O E A R : Type} [CommRing O] [CommRing E] [CommRing A] [CommRing R]
    [Algebra O E] [Algebra O A] [Algebra O R] {n : Type} [Fintype n] [DecidableEq n]
    (ι : A →ₐ[O] R) (p : ℕ) (τ : A) (φ : R →ₐ[O] R) (io : E →ₐ[O] R) (S : Subring R)
    (ht : IsUnit (ι τ)) (hp : 2 ≤ p)
    (h3 : ∀ m x, Near (ι : A →+* R) p (ι τ) m x → Near (ι : A →+* R) p (ι τ) (p * m) (φ x))
    (meet : ∀ x, (∀ m, Near (ι : A →+* R) p (ι τ) m x) → ∃ r, x = (p : R) * r)
    (comp : ∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) →
      (∀ i, Near (ι : A →+* R) p (ι τ) (i + k) (f i)) →
      ∃ x ∈ S, ∀ m, Near (ι : A →+* R) p (ι τ) (m + k) (x - ∑ i ∈ Finset.range m, f i))
    (hφS : ∀ x ∈ S, φ x ∈ S) (hioS : ∀ e, io e ∈ S)
    (hD : ∀ x ∈ modSub (io : E →+* R) p, (φ : R →+* R) x ∈ modSub (io : E →+* R) p)
    (hpole : ∀ x, ∃ k, Near (ι : A →+* R) p (ι τ) 0 ((ι τ) ^ k * x))
    (h2 : ∀ x ∈ S, ∀ m, ∃ u ∈ perfSub (φ : R →+* R) (modSub (io : E →+* R) p) hD,
      Near (ι : A →+* R) p (ι τ) m (x - u))
    (hφt : (p : R) ∣ (ι τ) ^ p - φ (ι τ)) (hJ : ∀ x : R, IsUnit (1 + (p : R) * x))
    {H : Type} (Q : H → Prop) (g : H → (R →ₐ[O] R)) (hS : ∀ x, x ∈ S ↔ ∀ h, Q h → g h x = x)
    (hsat : ∀ x, (p : R) * x ∈ S → x ∈ S)
    (sep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (compS : ∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ y ∈ S, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r)
    (compE : ∀ x : ℕ → E, ∃ y, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (p : E) ^ i * x i = (p : E) ^ k * r)
    (hrefl : ∀ e, IsUnit (io e) → IsUnit e)
    (F : Matrix n n R) (hF : ∀ i j, F i j ∈ S) (hu : IsUnit F) :
    ∃ (V : Matrix n n R) (e : Matrix n n E), IsUnit V ∧ (∀ i j, V i j ∈ S) ∧
      F * V.map φ = V * e.map io := by
  obtain ⟨e, V, h1, h2, h3⟩ := conj_io (ι := (ι : A →+* R)) (φ := (φ : R →+* R))
    (io := (io : E →+* R)) (τ := τ) rfl ht hp h3 meet comp hφS hioS hD hpole h2 hφt hJ
    (fun X Y hX hXY i j => (hS _).2 fun h hh => map_eq_of_mul_eq_one
      (g h : R →+* R) (fun i j => (hS _).1 (hX i j) h hh) hXY i j)
    hsat sep compS compE hrefl F hF hu
  exact ⟨V, e, h2, h1, h3⟩



theorem decompletion : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (r : ℕ) (F : Matrix (Fin r) (Fin r) (RW LL)), IsUnit F → (∀ i j, FixH AI K (F i j)) → ∃ (V : Matrix (Fin r) (Fin r) (RW LL)) (F' : Matrix (Fin r) (Fin r) R.EE), IsUnit V ∧ (∀ i j, FixH AI K (V i j)) ∧ F * V.map (φRW LL) = V * F'.map I.ioE := by
  intro l _ P AI K s LL h Γ R I hI r F hu hF
  have hl := GlobalTheory.Decompl.FixL.fixSub_ladic l P AI LL {g | g ∈ GK K ∧ P.χQ g = 1}
  obtain ⟨V, e, h1, h2, h3⟩ := conj_io' (inclR LL) l ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piW AI s) (φRW LL)
    I.ioE (fixSub AI LL {g | g ∈ GK K ∧ P.χQ g = 1})
    (isUnit_pi I)
    (Fact.out : l.Prime).two_le
    (near_φ AI LL s)
    (meet_RW AI LL s)
    (GlobalTheory.Decompl.fixSub_nearPi_complete l P AI LL s _ ((mem_fixSub_iff AI K _).2 (fixH_pi I)))
    hl.2.1
    (fun e => (mem_fixSub_iff AI K _).2 (fixH_io I e))
    (stable_io I l)
    (exists_pole_RW AI LL s)
    (fun x hx => exists_near_perfI h I hI x ((mem_fixSub_iff AI K _).1 hx))
    (dvd_pow_sub Fact.out (frob_pi I (P.PD_p K)))
    (isUnit_one_add_RW LL)
    (· ∈ {g | g ∈ GK K ∧ P.χQ g = 1}) (AI.gRW LL)
    (fun _ => mem_fixSub)
    hl.1
    (GlobalTheory.EtaleExact.sep_RW LL)
    hl.2.2
    (series_EE R (P.PD_p K))
    (GlobalTheory.IoInj.ioE_injective_saturated_inter l P AI K s LL h Γ R I hI).2.1
    F
    (fun i j => (mem_fixSub_iff AI K _).2 (hF i j))
    hu
  exact ⟨V, e, h1, fun i j => (mem_fixSub_iff AI K _).1 (h2 i j), h3⟩

end GlobalTheory.HWL.MatDecompl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtalePhiMatrixDecompletionToWachStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.etalePhiMatrix_decompletion_to_wach : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (r : ℕ) (F : Matrix (Fin r) (Fin r) (RW LL)), IsUnit F → (∀ i j, FixH AI K (F i j)) → ∃ (V : Matrix (Fin r) (Fin r) (RW LL)) (F' : Matrix (Fin r) (Fin r) R.EE), IsUnit V ∧ (∀ i j, FixH AI K (V i j)) ∧ F * V.map (φRW LL) = V * F'.map I.ioE := by
  first | exact @GlobalTheory.HWL.MatDecompl.decompletion | exact GlobalTheory.HWL.MatDecompl.decompletion | (intros; apply GlobalTheory.HWL.MatDecompl.decompletion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicKernelFixedBasisWittTensorLatticStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_cyclotomicKernelFixedBasis_wittTensorLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), FixBasis AI T e := by
  first | exact @GlobalTheory.HWL.FixedBasis.main | exact GlobalTheory.HWL.FixedBasis.main | (intros; apply GlobalTheory.HWL.FixedBasis.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRangeMap

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EtaleBasis

section Generic

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

theorem repr_of_fixed (e : Module.Basis (Fin r) R M) (τ : R →+* R) (A : M →+ M)
    (hA : ∀ c x, A (c • x) = τ c • A x) (he : ∀ i, A (e i) = e i) (x : M) (i : Fin r) :
    e.repr (A x) i = τ (e.repr x i) := by
  have h : A x = ∑ k, τ (e.repr x k) • e k := by
    conv_lhs => rw [← e.sum_repr x]

    simp only [map_sum, hA, he]
  rw [h, e.repr_sum_self]

theorem isUnit_matrix (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (hs : Submodule.span R (Set.range Φ) = ⊤) :
    IsUnit (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  have hle : Submodule.span R (Set.range Φ) ≤ Submodule.span R (Set.range fun j => Φ (e j)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩

    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hΦ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro y
  have hy : e.equivFun.symm y ∈ Submodule.span R (Set.range fun j => Φ (e j)) :=
    hle (hs ▸ Submodule.mem_top)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  refine ⟨c, funext fun i => ?_⟩
  have h1 : e.equivFun (e.equivFun.symm y) i = y i := by rw [LinearEquiv.apply_symm_apply]
  rw [← h1, ← hc]
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem change_basis (e : Module.Basis (Fin r) R M) (σ : R →+* R) (Φ : M →+ M)
    (hΦ : ∀ c x, Φ (c • x) = σ c • Φ x) (V F₁ : Matrix (Fin r) (Fin r) R) (hV : IsUnit V)
    (h : (Matrix.of fun i j => e.repr (Φ (e j)) i : Matrix (Fin r) (Fin r) R) * V.map σ = V * F₁) :
    ∃ e' : Module.Basis (Fin r) R M, (∀ j, e' j = ∑ i, V i j • e i) ∧
      ∀ i j, e'.repr (Φ (e' j)) i = F₁ i j := by
  obtain ⟨u, rfl⟩ := hV
  let L : M ≃ₗ[R] M := Matrix.toLinOfInv e e u.mul_inv u.inv_mul
  have hL : ∀ j, (e.map L) j = ∑ i, (u : Matrix (Fin r) (Fin r) R) i j • e i := by
    intro j
    simp [L, Matrix.toLinOfInv, Matrix.toLin_self]
  refine ⟨e.map L, hL, fun i j => ?_⟩
  have key : Φ ((e.map L) j) = ∑ k, F₁ k j • (e.map L) k := by
    apply e.repr.injective
    ext m
    have hm := congrFun (congrFun h m) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply] at hm

    simp [hL, map_sum, hΦ, map_smul, smul_eq_mul, Finsupp.single_apply]
    simpa only [mul_comm] using hm
  rw [key, Module.Basis.repr_sum_self]

end Generic

section Tensor

variable {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]

theorem map_smul_semi (f : R →ₐ[O] R) (a : N →ₗ[O] N) (c : R) (x : R ⊗[O] N) :
    TensorProduct.map f.toLinearMap a (c • x) = f c • TensorProduct.map f.toLinearMap a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul b t => simp [TensorProduct.smul_tmul']

theorem span_range_map (f : R →ₐ[O] R) :
    Submodule.span R (Set.range (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul b t =>
    have : b ⊗ₜ[O] t = b • TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) ((1 : R) ⊗ₜ[O] t) := by
      simp [TensorProduct.smul_tmul']
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem map_comm (f g : R →ₐ[O] R) (h : ∀ c, f (g c) = g (f c)) (a : N →ₗ[O] N) (x : R ⊗[O] N) :
    TensorProduct.map g.toLinearMap a (TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) x) =
      TensorProduct.map f.toLinearMap (LinearMap.id : N →ₗ[O] N) (TensorProduct.map g.toLinearMap a x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul b t => simp [h]

theorem descend {r : ℕ} {ι : Type} (φ : R →ₐ[O] R) (g : ι → (R →ₐ[O] R)) (a : ι → (N →ₗ[O] N))
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (R ⊗[O] N))
    (he : ∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (R ⊗[O] N),
      (∀ s i, TensorProduct.map (g s).toLinearMap (a s) (e' i) = e' i) ∧
      ∀ i j, e'.repr (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N) (e' j)) i ∈ S := by
  let Φ : R ⊗[O] N →+ R ⊗[O] N :=
    (TensorProduct.map φ.toLinearMap (LinearMap.id : N →ₗ[O] N)).toAddMonoidHom
  have hΦ : ∀ (c : R) x, Φ (c • x) = (φ : R →+* R) c • Φ x := map_smul_semi φ _
  obtain ⟨V, F₁, hV, hVg, hS, hE⟩ := dec _ (isUnit_matrix e φ Φ hΦ (span_range_map φ)) (by
    intro i j s
    have h1 := repr_of_fixed e (g s : R →+* R)
      (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (map_smul_semi (g s) _) (he s) (Φ (e j)) i
    have h2 : (TensorProduct.map (g s).toLinearMap (a s)).toAddMonoidHom (Φ (e j)) = Φ (e j) := by
      have := map_comm φ (g s) (hc s) (a s) (e j)
      rw [he] at this
      exact this
    rw [h2] at h1
    exact h1.symm)
  obtain ⟨e', h1, h2⟩ := change_basis e φ Φ hΦ V F₁ hV hE
  refine ⟨e', fun s j => ?_, fun i j => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul_semi, hVg, he]
  · have := hS i j
    rw [← h2] at this
    exact this

end Tensor

theorem descend_lat {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R] [Algebra O R]
    (T : LocLat G Qp LL O) {r : ℕ} (φ : R →ₐ[O] R) (g : G → (R →ₐ[O] R)) (H : G → Prop)
    (hc : ∀ s c, φ (g s c) = g s (φ c)) (S : Set R)
    (dec : ∀ F : Matrix (Fin r) (Fin r) R, IsUnit F → (∀ i j s, H s → g s (F i j) = F i j) →
      ∃ V F₁ : Matrix (Fin r) (Fin r) R, IsUnit V ∧ (∀ i j s, H s → g s (V i j) = V i j) ∧
        (∀ i j, F₁ i j ∈ S) ∧ F * V.map φ = V * F₁)
    (e : Module.Basis (Fin r) R (TW R T)) (he : ∀ s, H s → ∀ i, TWact (g s) T s (e i) = e i) :
    ∃ e' : Module.Basis (Fin r) R (TW R T), (∀ s, H s → ∀ i, TWact (g s) T s (e' i) = e' i) ∧
      ∀ i j, e'.repr (TWmap φ T (e' j)) i ∈ S := by
  obtain ⟨e', h1, h2⟩ := descend (ι := {s : G // H s}) φ (fun s => g s.1) (fun s => T.actT s.1)
    (fun s c => hc s.1 c) S
    (fun F hU hfix => by
      obtain ⟨V, F₁, hV, hVf, hS, hE⟩ := dec F hU (fun i j s hs => hfix i j ⟨s, hs⟩)
      exact ⟨V, F₁, hV, fun i j s => hVf i j s.1 s.2, hS, hE⟩)
    e (fun s i => he s.1 s.2 i)
  exact ⟨e', fun s hs i => h1 ⟨s, hs⟩ i, h2⟩

theorem map_id_comm {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O]
    [Algebra Z W] (f g : W →ₐ[Z] W) (h : ∀ w, f (g w) = g (f w)) (x : O ⊗[Z] W) :
    Algebra.TensorProduct.map (AlgHom.id O O) f (Algebra.TensorProduct.map (AlgHom.id O O) g x) =
    Algebra.TensorProduct.map (AlgHom.id O O) g (Algebra.TensorProduct.map (AlgHom.id O O) f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a w => simp [h]

theorem frob_comm_gal {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (g : GQ l)
    (x : RW LL) : φRW LL (AI.gRW LL g x) = AI.gRW LL g (φRW LL x) := by
  refine map_id_comm _ _ (fun w => ?_) x
  ext n
  change (WittVector.map (frobenius (Cb l) l)
      (WittVector.map (autCb l (AI.actT g)).toRingHom w)).coeff n =
    (WittVector.map (autCb l (AI.actT g)).toRingHom (WittVector.map (frobenius (Cb l) l) w)).coeff n
  simp [WittVector.map_coeff, frobenius_def]

theorem fixH_iff {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {LL : FinExt l}
    (x : RW LL) : FixH AI K x ↔ ∀ g : ↥(GK K), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) x = x := by
  unfold FixH
  constructor
  · intro h g hχ
    exact h g.1 g.2 hχ
  · intro h g hg hχ
    have h1 := h ⟨g, hg⟩
    dsimp only at h1
    exact h1 hχ

theorem decomplete {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (hG : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (hI : IoW I) (r : ℕ)
    (F : Matrix (Fin r) (Fin r) (RW LL)) (hU : IsUnit F)
    (hfix : ∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (F i j) = F i j) :
    ∃ V F₁ : Matrix (Fin r) (Fin r) (RW LL),
      IsUnit V ∧ (∀ i j (g : ↥(GK K)), P.χQ (g : GQ l) = 1 → AI.gRW LL (g : GQ l) (V i j) = V i j) ∧
      (∀ i j, F₁ i j ∈ Set.range I.ioE) ∧ F * V.map (φRW LL) = V * F₁ := by
  have h0 : ∀ i j, FixH AI K (F i j) := fun i j => (fixH_iff AI K _).mpr (hfix i j)
  have h1 := GlobalTheory.T.etalePhiMatrix_decompletion_to_wach l P AI K s LL hG Γ R I hI r F hU h0
  obtain ⟨V, F', hV, hVf, hE⟩ := h1
  refine ⟨V, F'.map I.ioE, hV, fun i j => (fixH_iff AI K _).mp (hVf i j), ?_, hE⟩
  intro i j
  rw [Matrix.map_apply]
  exact Set.mem_range_self _

theorem exists_etBasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), FaithH AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), ∃ e : Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (RW LL) (TW (RW LL) T), EtBasis I T e := by
  intro l _ P AI hF K s LL hG Γ R I hI T
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_cyclotomicKernelFixedBasis_wittTensorLattice l P AI hF K LL T
  unfold EtBasis FixBasis
  unfold FixBasis at he
  exact descend_lat T (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l)) (fun g => P.χQ (g : GQ l) = 1)
    (fun g c => frob_comm_gal AI LL (g : GQ l) c) (Set.range I.ioE)
    (decomplete AI K s LL hG Γ R I hI _) e he

end GlobalTheory.EtaleBasis
end
end
