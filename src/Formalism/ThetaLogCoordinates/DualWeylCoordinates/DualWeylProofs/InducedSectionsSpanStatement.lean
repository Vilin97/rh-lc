module

public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhDetZpowMem
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementH
public import Formalism.GradedWeylDivisibility.FinalC
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhCountAll
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhEquivOfCount

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      exact (not_le.mpr hc) (hm.2.trans (hmu hmt))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
  · intro h
    have hsub : Finset.Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ m, h.trans (hmu hm)⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega

lemma qh_le_last [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  rw [Fin.le_iff_val_le_val]
  show a.val ≤ n - 1
  have := a.isLt
  omega

lemma qh_count [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) :
    ((TCols mu).filter (fun c => t.val < colH mu c)).card = (mu t - mu (lastIdx n)).toNat := by
  have h0 : mu t ≤ mu 0 := hmu (by first | exact Fin.zero_le _ | (rw [Fin.le_iff_val_le_val]; simp))
  have hset : (TCols mu).filter (fun c => t.val < colH mu c) =
      Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    simp only [Finset.mem_filter, qh_lt_colH_iff hmu, TCols, Finset.mem_Ioc]
    exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2.trans h0⟩, hh.2⟩⟩
  rw [hset, Int.card_Ioc]

lemma qh_weight_sum [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun _ : Fin n => mu (lastIdx n)) +
      ∑ c : ↥(TCols mu), (fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0) = mu := by
  funext a
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_coe_sort (TCols mu) (fun c => if a.val < colH mu c then (1 : ℤ) else 0),
    Finset.sum_boole, qh_count hmu a,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmu (qh_le_last a)))]
  ring

lemma qh_mapCoord_alg (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ _ P) = algebraMap _ _ (MvPolynomial.map (Int.castRingHom R) P) := by
  first
    | (rw [mapCoord, IsLocalization.Away.AwayMap.lift_eq]; try rfl; done)
    | (rw [mapCoord, IsLocalization.Away.lift_eq]; try rfl; done)
    | (simp [mapCoord]; done)
    | (unfold mapCoord; exact IsLocalization.lift_eq _ _)

lemma qh_mapCoord_detU (z : ℤ) :
    mapCoord R ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qhDet R n ^ z : (GLCoord R n)ˣ) : GLCoord R n) := by
  have h1 : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    apply Units.ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R)) (genMat ℤ n),
      genMat_map_coord]
  rw [← h1, ← map_zpow (Units.map (mapCoord (n := n) R).toMonoidHom) (detU n) z, Units.coe_map]
  try rfl

lemma qh_can_emb [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have hmem : ∀ x : Fin (colH mu c), Fin.castLE (colH_le mu c) x ∈ (canT mu c).1 := by
    intro x
    first
      | (simp only [canT, Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨x, rfl⟩)
      | simp [canT]
  have hmono : StrictMono (Fin.castLE (colH_le mu c)) := by
    intro x y hxy
    rw [Fin.lt_iff_val_lt_val] at hxy ⊢
    exact hxy
  exact (congrFun (Finset.orderEmbOfFin_unique (canT mu c).2 hmem hmono) a).symm

lemma qh_mapCoord_minor [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (S : Finset (Fin n))
    (hS : S.card = colH mu c) :
    mapCoord R (minorC (canT mu c).1 S (canT mu c).2 hS) =
      qhN R (colH mu c) (colH_le mu c) (fun q => S.orderEmbOfFin hS q) := by
  unfold minorC qhN
  rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R))]
  congr 2
  ext p q
  first
    | (simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, genMat, MvPolynomial.map_X,
        qh_can_emb]; done)
    | simp [genMat, qh_can_emb]

lemma qh_mapCoord_brk [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord R (brk mu I) = ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
      ∏ c : ↥(TCols mu), qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q) := by
  first
    | (simp only [brk, TMat]
       rw [map_mul, map_prod, qh_mapCoord_detU]
       congr 1
       refine Finset.prod_congr rfl (fun c _ => ?_)
       exact qh_mapCoord_minor mu c _ _)
    | (simp only [brk, TMat, map_mul, map_prod, qh_mapCoord_detU,
        qh_mapCoord_minor])

lemma qh_brk_mem [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    mapCoord R (brk mu I) ∈ inducedSections R mu := by
  rw [qh_mapCoord_brk]
  have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) (mu (lastIdx n)))
    (qh_prod_mem (R := R) (Finset.univ : Finset ↥(TCols mu))
      (fun c => qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q))
      (fun c => fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0)
      (fun c _ => qh_N_mem (R := R) (colH mu c) (colH_le mu c) _))
  first
    | (rw [qh_weight_sum hmu] at h; exact h)
    | (convert h using 2; exact (qh_weight_sum hmu).symm)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
end

-- Source module: Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhMemDualWeyl

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_generic {B : Type} [CommRing B] [IsDomain B] [Algebra R B] (bm gm : Matrix (Fin n) (Fin n) B)
    (hb : ∀ a c, a < c → bm a c = 0) (hbd : ∀ a, bm a a ≠ 0) (hg : gm.det ≠ 0)
    (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    aeval (fun v : Fin n × Fin n => (bm * gm) v.2 v.1) Q =
      (∏ a, bm a a ^ ν a) * aeval (fun v : Fin n × Fin n => gm v.2 v.1) Q := by
  let F := FractionRing B
  let φ : B →+* F := algebraMap B F
  have hinj : Function.Injective φ := IsFractionRing.injective B F
  have hbdet : (φ.mapMatrix bm).det ≠ 0 := by
    rw [← RingHom.map_det, Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij),
      map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hbd a
  have hgdet : (φ.mapMatrix gm).det ≠ 0 := by
    rw [← RingHom.map_det, map_ne_zero_iff _ hinj]; exact hg
  let b' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hbdet
  let g' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hgdet
  have hb' : b'.val = φ.mapMatrix bm := rfl
  have hg' : g'.val = φ.mapMatrix gm := rfl
  have h := hQ F b' g' (by intro a c hac; rw [hb']; show φ (bm a c) = 0; rw [hb a c hac, map_zero])
  have hev : ∀ (M : Matrix (Fin n) (Fin n) B) (h' : GL (Fin n) F), h'.val = φ.mapMatrix M →
      evGLR h' (algebraMap _ (GLCoord R n) (rename Prod.swap Q)) =
        φ (aeval (fun v : Fin n × Fin n => M v.2 v.1) Q) := by
    intro M h' hh
    rw [qh_evGLR_alg, coe_eval₂Hom, eval₂_rename, aeval_def, eval₂_comp_left, hh]
    rw [IsScalarTower.algebraMap_eq R B F]
    rfl
  rw [hev (bm * gm) (b' * g') (by rw [Units.val_mul, hb', hg', map_mul]), hev gm g' hg'] at h
  apply hinj
  rw [map_mul, map_prod]
  simp only [map_pow]
  simpa [hb'] using h

lemma qh_det_ne [IsDomain R] {B : Type} [CommRing B] (φ : MvPolynomial (Fin n × Fin n) R →+* B)
    (hφ : Function.Injective φ) : (Matrix.of fun a c : Fin n => φ (X (c, a))).det ≠ 0 := by
  have h : (Matrix.of fun a c : Fin n => φ (X (c, a))) =
      (φ.mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) R)).transpose := by
    ext a c; simp [Matrix.mvPolynomialX]
  rw [h, Matrix.det_transpose, ← RingHom.map_det, map_ne_zero_iff _ hφ]
  exact Matrix.det_mvPolynomialX_ne_zero _ _

def qhPhi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  aeval fun v : Fin n × Fin n => X v.2 * C (X v)

lemma qh_phi_mono1 (d : Fin n × Fin n →₀ ℕ) :
    qhPhi R n (monomial d 1) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d 1) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 =>
    have e : (monomial (d1 + d2) (1 : R)) = monomial d1 1 * monomial d2 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, h1, h2, monomial_mul, Finsupp.mapDomain_add]
  | single v e =>
    rw [← X_pow_eq_monomial, map_pow, qhPhi, aeval_X, mul_pow, Finsupp.mapDomain_single, ← map_pow,
      X_pow_eq_monomial, mul_comm, C_mul_monomial, mul_one]

lemma qh_phi_mono (d : Fin n × Fin n →₀ ℕ) (r : R) :
    qhPhi R n (monomial d r) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d r) := by
  have e : monomial d r = r • monomial d (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, qh_phi_mono1, smul_monomial]

lemma qh_phi_coeff (Q : MvPolynomial (Fin n × Fin n) R) (d0 : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff (qhPhi R n Q) (Finsupp.mapDomain Prod.snd d0)) d0 = AddMonoidAlgebra.coeff Q d0 := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [qh_phi_mono]
    by_cases h : d = d0
    · subst h; simp
    · rw [coeff_monomial, coeff_monomial, if_neg h]
      split_ifs
      · rw [coeff_monomial, if_neg h]
      · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

lemma qh_weight (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) d = ⇑(Finsupp.mapDomain Prod.snd d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 => rw [map_add (f := _), h1, h2, Finsupp.mapDomain_add, Finsupp.coe_add]
  | single v e =>
    rw [Finsupp.weight_single, Finsupp.mapDomain_single]
    funext a
    simp [Formalism.GradedWeylDivisibility.colW, Finsupp.single_apply, Pi.single_apply, eq_comm]

lemma qh_homog [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) Q ν := by
  have h := qh_generic (B := MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))
    (Matrix.diagonal fun a => X a) (Matrix.of fun a c : Fin n => C (X (c, a)))
    (fun a c hac => Matrix.diagonal_apply_ne _ hac.ne) (fun a => by simp)
    (qh_det_ne (C : _ →+* MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R)) (C_injective _ _)) Q ν hQ
  have e1 : aeval (fun v : Fin n × Fin n => ((Matrix.diagonal fun a => X a) *
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = qhPhi R n Q := by
    rw [qhPhi]; congr 2; funext v; simp [Matrix.diagonal_mul]
  have e2 : aeval (fun v : Fin n × Fin n =>
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = C Q := by
    have := MvPolynomial.comp_aeval_apply (R := R) (fun v : Fin n × Fin n => (X v : MvPolynomial (Fin n × Fin n) R))
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) Q
    rw [aeval_X_left_apply] at this
    exact this.symm
  have e3 : (∏ a, (Matrix.diagonal fun a => (X a : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) a a ^ ν a) =
      monomial (Finsupp.equivFunOnFinite.symm ν) 1 := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  rw [e1, e2, e3, mul_comm, C_mul_monomial, mul_one] at h
  intro d hd
  rw [qh_weight]
  by_contra hne
  apply hd
  have hne' : Finsupp.equivFunOnFinite.symm ν ≠ Finsupp.mapDomain Prod.snd d := by
    intro heq
    apply hne
    rw [← heq]; rfl
  rw [← qh_phi_coeff, h, coeff_monomial, if_neg hne']
  simp

lemma qh_invariant [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ)))
    (l j : Fin n) (hlj : l < j) :
    Formalism.GradedWeylDivisibility.colAddGen R l j Q = rename some Q := by
  have h := qh_generic (B := MvPolynomial (Option (Fin n × Fin n)) R)
    (Matrix.transvection j l (X none)) (Matrix.of fun a c : Fin n => X (some (c, a)))
    (fun a c hac => by
      have : ¬ (j = a ∧ l = c) := by rintro ⟨rfl, rfl⟩; exact absurd hlj (not_lt.2 hac.le)
      simp [Matrix.transvection, hac.ne, this])
    (fun a => by
      have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
      simp [Matrix.transvection, this])
    (qh_det_ne (rename some : MvPolynomial (Fin n × Fin n) R →ₐ[R] _).toRingHom
      (rename_injective _ (Option.some_injective _)) |> fun h => by simpa using h) Q ν hQ
  have e3 : (∏ a, (Matrix.transvection j l (X none : MvPolynomial (Option (Fin n × Fin n)) R)) a a ^ ν a) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
    simp [Matrix.transvection, this]
  rw [e3, one_mul] at h
  have e1 : Formalism.GradedWeylDivisibility.colAddGen R l j Q = aeval (fun v : Fin n × Fin n => ((Matrix.transvection j l (X none)) *
      (Matrix.of fun a c : Fin n => (X (some (c, a)) : MvPolynomial (Option (Fin n × Fin n)) R)) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Option (Fin n × Fin n)) R)) v.2 v.1) Q := by
    rw [Formalism.GradedWeylDivisibility.colAddGen]; congr 2; funext v
    by_cases hv : v.2 = j
    · rw [if_pos hv, hv, Matrix.transvection_mul_apply_same]
      simp [← hv]
    · rw [if_neg hv, Matrix.transvection_mul_apply_of_ne _ _ _ _ hv]
      simp
  rw [e1, h, ← aeval_X_left_apply (rename some Q), aeval_rename]
  rfl

lemma qh_mem_dualWeyl [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf]
  refine ⟨qh_homog Q ν hQ, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro l j hlj
  exact qh_invariant Q ν hQ l j hlj

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
end

-- Source module: Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement

section

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_reduce [IsDomain R] (mu : Fin n → ℤ) (f : GLCoord R n) (hf : f ∈ inducedSections R mu) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin n × Fin n) R), (∀ a, 0 ≤ mu a + k) ∧
      f = ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
        algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∧
      Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n (fun a => (mu a + k).toNat) := by
  obtain ⟨N, P, hNP⟩ := IsLocalization.Away.surj (genMat R n).det f
  have hk : ∀ a, 0 ≤ mu a + ((N + (Finset.univ.sup fun b => (-mu b).toNat) : ℕ) : ℤ) := by
    intro a
    have h1 := Int.self_le_toNat (-mu a)
    have h2 : (-mu a).toNat ≤ Finset.univ.sup fun b => (-mu b).toNat :=
      Finset.le_sup (f := fun b => (-mu b).toNat) (Finset.mem_univ a)
    push_cast
    omega
  set M : ℕ := Finset.univ.sup fun b => (-mu b).toNat with hM
  have hswap : rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M)) = P * (genMat R n).det ^ M := by
    rw [rename_rename, Prod.swap_swap_eq, rename_id_apply]
  have hmain : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) =
      f * algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [hswap, map_mul, map_pow, pow_add, ← mul_assoc, hNP]
  have hunit : ((qhDet R n ^ ((N + M : ℕ) : ℤ) : (GLCoord R n)ˣ) : GLCoord R n) =
      algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qhDet_val]
  refine ⟨N + M, rename Prod.swap (P * (genMat R n).det ^ M), hk, ?_, ?_⟩
  · rw [hmain, ← hunit, mul_comm f, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul]
  · have hmem : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) ∈
        inducedSections R (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) := by
      rw [hmain, mul_comm, ← hunit]
      have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) ((N + M : ℕ) : ℤ)) hf
      have e : (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) = (fun _ : Fin n => ((N + M : ℕ) : ℤ)) + mu := by
        funext a
        rw [Pi.add_apply, Int.toNat_of_nonneg (hk a), add_comm]
      rw [e]
      exact h
    exact qh_mem_dualWeyl _ _ hmem

lemma qh_span_transfer (T : Submodule R (GLCoord R n)) (u : GLCoord R n)
    (S : Set (MvPolynomial (Fin n × Fin n) R))
    (h : ∀ x ∈ S, u * algebraMap _ (GLCoord R n) (rename Prod.swap x) ∈ T)
    (Q : MvPolynomial (Fin n × Fin n) R) (hQ : Q ∈ Submodule.span R S) :
    u * algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ T := by
  let L : MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
    (LinearMap.mulLeft R u).comp ((IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap.comp
      (rename Prod.swap).toLinearMap)
  have hle : Submodule.span R S ≤ T.comap L := Submodule.span_le.mpr (fun x hx => h x hx)
  exact hle hQ

private theorem antitone_of_step_lemma {n : ℕ} (g : Fin n → ℤ) (h : ∀ l j : Fin n, (j : ℕ) = l + 1 → g j ≤ g l) :
    Antitone g := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl).trans (ih (by omega))

theorem highest_weight_corollary_one : InducedSectionsSpanStatement := by
  intro n _ mu R _ _ _
  constructor
  · intro hmu
    apply Set.Subset.antisymm
    · intro f hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n] at hQ
      rw [SetLike.mem_coe, hfQ]
      refine qh_span_transfer (Submodule.span R (Set.range fun I : TIdx mu => mapCoord R (brk mu I))) _ _ ?_ Q hQ
      rintro x ⟨K, sz, hsz, I, hsh, rfl⟩
      exact qh_bidet_mem hmu k (hk _) sz hsz I (fun t => by rw [hsh]; exact Int.toNat_of_nonneg (hk t))
    · exact qh_span_le (by rintro _ ⟨I, rfl⟩; exact qh_brk_mem hmu I)
  · intro hmu
    ext f
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      by_contra hf0
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        apply hf0
        rw [hfQ]
        simp
      apply hmu
      have hInt := Formalism.GradedWeylDivisibility.leadInterlaced R n n _ Q hQ hQ0
      have hcol := Formalism.GradedWeylDivisibility.colSums R n n _ Q hQ _ (MonomialOrder.degree_mem_support (m := Formalism.GradedWeylDivisibility.colLex n n) hQ0)
      set m := (Formalism.GradedWeylDivisibility.colLex n n).degree Q
      apply antitone_of_step_lemma mu
      intro l j hlj
      have hI : Formalism.GradedWeylDivisibility.InterlacedAt 0 l j m := hInt l j hlj
      have hI2 := hI (lastIdx n)
      have e1 : (∑ b : Fin n with b ≤ lastIdx n, m (b, j)) = ∑ b, m (b, j) := by
        rw [Finset.filter_true_of_mem (fun b _ => qh_le_last b)]
      have e2 : (∑ b : Fin n with b < lastIdx n, m (b, l)) ≤ ∑ b, m (b, l) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have cj := hcol j
      have cl := hcol l
      have tj := Int.toNat_of_nonneg (hk j)
      have tl := Int.toNat_of_nonneg (hk l)
      omega
    · rintro rfl
      exact qh_zero_mem mu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
end
