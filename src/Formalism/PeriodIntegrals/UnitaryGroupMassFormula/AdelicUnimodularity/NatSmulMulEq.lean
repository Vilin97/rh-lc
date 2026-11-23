module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.IsCompactCset
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.SmulEqAlgebraMapMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.LamAfLeOhatL

section

@[expose] public section

noncomputable section

namespace PI.WAU

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af F) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) (Af F) (l i)}

theorem smul_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af F} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  let T : Subring (E ⊗[F] Af F) :=
    { carrier := {a | ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L}
      mul_mem' := fun {a c} ha hc y hy => by rw [mul_smul]; exact ha _ (hc y hy)
      one_mem' := fun y hy => by rw [one_smul]; exact hy
      add_mem' := fun {a c} ha hc y hy => by rw [add_smul]; exact add_mem (ha y hy) (hc y hy)
      zero_mem' := fun y _ => by rw [zero_smul]; exact zero_mem _
      neg_mem' := fun {a} ha y hy => by rw [neg_smul]; exact neg_mem (ha y hy) }
  have hle : IntAf F E ≤ T := by
    apply Subring.closure_le.mpr
    rintro a (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := hx
      refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c, hc, o • l, L.smul_mem o hl, ?_⟩
        funext i
        show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Af F)) * (((1 : E) ⊗ₜ[F] c) * ((l i) ⊗ₜ[F] (1 : Af F))) =
          ((1 : E) ⊗ₜ[F] c) * (((o • l) i) ⊗ₜ[F] (1 : Af F))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Pi.smul_apply, Algebra.smul_def]
        simp only [one_mul, mul_one]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
    · refine fun y hy => ?_
      unfold ohatL at hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hz
        apply AddSubgroup.subset_closure
        refine ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add u w _ _ hu hw => rw [smul_add]; exact add_mem hu hw
      | neg u _ hu => rw [smul_neg]; exact neg_mem hu
  exact hle ha

theorem lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af F}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨1, ohat_one, (l : Fin n → E), l.2, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x z _ _ hx hz => exact add_mem hx hz
  | smul a x _ hx => exact smul_ohatL L a.2 x hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af F) := by
  intro k
  simp only [map_zero, Pi.zero_apply]
  exact ohat_zero

theorem intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af F} (hx : IntC b x) : IntC b (-x) := by
  intro k
  simp only [map_neg, Pi.neg_apply]
  exact ohat_neg (hx k)

theorem exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨T, hT⟩ := (hfg.restrictScalars (R := ℤ))
  obtain ⟨D, hD, hDint⟩ := exists_den_fin (fun x : T × Fin n × ι =>
    b.repr ((x.1 : Fin n → E) x.2.1) x.2.2)
  have hQ : ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
    intro l hl
    have hl' : l ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by rw [hT]; exact hl
    clear hl
    induction hl' using Submodule.span_induction with
    | mem x hx => intro j k; exact hDint ⟨⟨x, hx⟩, j, k⟩
    | zero =>
      intro j k
      unfold IntF
      simp only [Pi.zero_apply, map_zero, Finsupp.coe_zero, mul_zero]
      exact ohat_zero
    | add x z _ _ hx hz =>
      intro j k
      have h1 := hx j k
      have h2 := hz j k
      unfold IntF at h1 h2 ⊢
      rw [Pi.add_apply, map_add (f := _), Finsupp.add_apply, mul_add, map_add (f := _)]
      exact ohat_add h1 h2
    | smul a x _ hx =>
      intro j k
      have h1 := hx j k
      unfold IntF at h1 ⊢
      rw [Pi.smul_apply, map_zsmul, Finsupp.smul_apply, mul_smul_comm, map_zsmul]
      exact ohat_zsmul h1 a
  refine ⟨D, hD, fun y hy j => ?_⟩
  have hy' := lamAf_le_ohatL L hy
  clear hy
  unfold ohatL at hy'
  induction hy' using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, l, hl, rfl⟩ := hz
    intro k
    rw [map_nsmul, Pi.smul_apply]
    have ew : ((((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) (Af F) (l i)) j) =
        (l j) ⊗ₜ[F] c := by
      simp [Formalism.UG.inclE, Algebra.TensorProduct.tmul_mul_tmul]
    rw [ew]
    simp only [coord, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
    rw [← Nat.cast_smul_eq_nsmul F, smul_smul, Algebra.smul_def]
    exact ohat_mul (hQ l hl j k) hc
  | zero => rw [Pi.zero_apply, smul_zero]; exact intC_zero
  | add u w _ _ hu hw => rw [Pi.add_apply, smul_add]; exact intC_add hu hw
  | neg u _ hu => rw [Pi.neg_apply, smul_neg]; exact intC_neg hu

end PI.WAU
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq

section

@[expose] public section

noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

private theorem intC_smul_entry_of_preserves_Lf (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hg : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F,
      v ∈ I.Lf ↔ (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf)
    (i j : Fin I.n) :
    IntC (bs I) ((D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j) := by
  classical
  have hy : ∀ j', IntC (bs I)
      ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) j') := by
    intro j'
    by_cases h : j' = j
    · rw [h, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne h]
      intro k
      simp only [map_zero, Pi.zero_apply]
      exact (Formalism.UG.intAd I.F).zero_mem
  have hL := (hg _).mp (hlow _ hy)
  have hI := hup _ hL i
  have hs : ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F)) i =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j * (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : D • ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply, hs]
    simp only [nsmul_eq_mul, Nat.cast_mul, mul_one]
    ring
  rwa [key] at hI

private theorem coord_mem_Bx_of_intC_nsmul (N : ℕ) (hN : 0 < N) (z : I.E ⊗[I.F] Af I.F)
    (hz : IntC (bs I) (N • z)) (k : ιb I) : coord (bs I) z k ∈ Bx I N := by
  simp only [Bx, Set.mem_image]
  refine ⟨N • coord (bs I) z k, ?_, ?_⟩
  · have := hz k
    rwa [map_nsmul, Pi.smul_apply] at this
  · have hN' : (N : I.F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)) N, ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]

theorem mem_range_psi (d D D1 : ℕ) (hN : 0 < D * (d * D1))
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) : ∃ p, psi I (D * (d * D1)) p = x := by
  classical
  have h0 : (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf := hx
  have h0i : ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹) ∈ Formalism.UG.stabGL I.Lf := inv_mem h0
  have hx' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v
        ∈ I.Lf := h0
  have hxi' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf := h0i
  have hm1 : matOf I (fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  have hm2 : matOf I (fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  refine ⟨⟨(fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j), fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)), ?_⟩, ?_⟩
  · simp only [Cset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j k
      exact ⟨coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hx' i j) k,
        coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hxi' i j) k⟩
    · rw [hm1, hm2]; exact Units.mul_inv _
    · rw [hm1, hm2]; exact Units.inv_mul _
    · rw [hm1]; exact x.2
    · intro l hl
      rw [hm1]
      exact (hx' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
    · intro l hl
      rw [hm2]
      exact (hxi' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
  · exact Subtype.ext (Units.ext hm1)

theorem nat_smul_mul_eq (g d D m : ℕ) (a y : I.E ⊗[I.F] Af I.F) :
    ((g * d * D * m) • a) * y = (g * d) • (m • (a * (D • y))) := by
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

theorem continuous_psi (N d D m : ℕ) (hd : 0 < d) (hD : 0 < D) (hm : 0 < m)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j))
    (hmul : ∀ x y : I.E ⊗[I.F] Af I.F, IntC (bs I) x → IntC (bs I) y → IntC (bs I) (m • (x * y))) :
    Continuous (psi I N) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  intro U hU
  have hV : (fun z => psi I N p * z) ⁻¹' U ∈ 𝓝 (1 : I.Gf) := by
    have := (continuous_const_mul (psi I N p)).tendsto 1
    rw [mul_one] at this
    exact this hU
  obtain ⟨g, hg1, hsub⟩ := I.topf_basis _ hV
  have hN1' : ((g * d * D * m : ℕ) : I.F) ≠ 0 := by
    have : 0 < g * d * D * m := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg1 hd) hD) hm
    exact_mod_cast this.ne'
  let c : I.F := ((g * d * D * m : ℕ) : I.F)⁻¹
  let W : Set (Cset I N) := {p' | ∀ i j k, algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k) ∈ Ohat I.F}
  have hW : W ∈ 𝓝 p := by
    have hWo : IsOpen W := by
      have : W = ⋂ i, ⋂ j, ⋂ k, (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) ⁻¹'
          Ohat I.F := by
        ext; simp [W]
      rw [this]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have h0 : Continuous (fun p' : Cset I N => p'.1.1 i j k) := by fun_prop
      have hc : Continuous (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) :=
        continuous_const.mul (h0.sub continuous_const)
      exact hc.isOpen_preimage _ isOpen_Ohat
    exact hWo.mem_nhds (fun i j k => by simpa using ohat_zero)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hW fun p' hp' => ?_
  have hQM : matOf I p.1.2 * matOf I p.1.1 = 1 := p.2.2.2.1
  let x := (psi I N p)⁻¹ * psi I N p'
  have hxK : x ∈ I.Kset :=
    (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem (psi_mem I N p)) (psi_mem I N p')
  have hfx : I.fmat x = matOf I p.1.2 * matOf I p'.1.1 := rfl
  have hcond : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    let u : Co I := fun i j k => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)
    have hu : ∀ i j k, u i j k ∈ Ohat I.F := hp'
    have hδ : ∀ i j, matOf I p'.1.1 i j - matOf I p.1.1 i j = (g * d * D * m) • emb (bs I) (u i j) := by
      intro i j
      simp only [matOf]
      rw [← emb_sub, ← emb_nsmul]
      congr 1; funext k
      simp only [u, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, c]
      rw [← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hN1', map_one,
        one_mul]
    let w : Fin I.n → I.E ⊗[I.F] Af I.F := fun i => ∑ j, m • (emb (bs I) (u i j) * (D • y j))
    have hw : ∀ i, IntC (bs I) (w i) := fun i => intC_sum _ fun j _ =>
      hmul _ _ (fun k => by rw [coord_emb]; exact hu i j k) (hup y hy j)
    have hdw := hlow w hw
    have hmv : (matOf I p'.1.1 - matOf I p.1.1) *ᵥ y = (g * d) • w := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, hδ, nat_smul_mul_eq I, Pi.smul_apply,
        Finset.smul_sum, w]
    refine ⟨matOf I p.1.2 *ᵥ (d • w), mulVec_mem_Lf I _ p.2.2.2.2.2.2 _ hdw, ?_⟩
    rw [hfx, ← hQM, ← Matrix.mul_sub, ← Matrix.mulVec_mulVec, hmv, mul_smul, Matrix.mulVec_smul,
      Nat.cast_smul_eq_nsmul]
  have hx := hsub ⟨hxK, hcond⟩
  show psi I N p' ∈ U
  have : psi I N p * x = psi I N p' := mul_inv_cancel_left _ _
  rw [← this]; exact hx

theorem isCompact_Kset : IsCompact I.Kset := by
  obtain ⟨d, hd, hlow⟩ := exists_lower (bs I) I.L I.L_span
  obtain ⟨D, hD, hup⟩ := exists_upper (bs I) I.L I.L_fg
  obtain ⟨m, hm, hmul⟩ := exists_den_mul (bs I)
  obtain ⟨D1, hD1, h1F⟩ := exists_den_fin (fun k : ιb I => (bs I).repr 1 k)
  have h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    intro k
    rw [map_nsmul, ← map_one (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := I.E) (B := Af I.F)),
      coord_incl, Pi.smul_apply, nsmul_eq_mul, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul]
    exact h1F k
  have hN : 0 < D * (d * D1) := Nat.mul_pos hD (Nat.mul_pos hd hD1)
  haveI : CompactSpace (Cset I (D * (d * D1))) :=
    isCompact_iff_compactSpace.mp (isCompact_Cset I _ d hd hlow)
  have : I.Kset = Set.range (psi I (D * (d * D1))) := by
    ext x
    constructor
    · intro hx; exact mem_range_psi I d D D1 hN hlow hup h1 hx
    · rintro ⟨p, rfl⟩; exact psi_mem I _ p
  rw [this]
  exact isCompact_range (continuous_psi I _ d D m hd hD hm hlow hup hmul)

end Cpt

end PI.WAU
end
end
end
