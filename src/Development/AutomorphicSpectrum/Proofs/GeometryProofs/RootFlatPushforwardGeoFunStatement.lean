module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyMultilinearStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArMonoAddSingle

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top

namespace RootMono

theorem card_fiber {α : Type*} [DecidableEq α] (l : List α) (c : α) :
    Fintype.card {i : Fin l.length // l.get i = c} = l.count c := by
  rw [Fintype.card_subtype, Finset.card_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := Fin.sum_univ_succ (n := l.length)
      (fun i : Fin (l.length + 1) => if (a :: l).get i = c then 1 else 0)
    simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ] at h ih
    simp only [List.get_eq_getElem, List.length_cons]
    rw [h, ih, List.count_cons]
    by_cases hac : a = c
    · simp [hac, add_comm]
    · simp [hac, add_comm]

theorem exists_perm_fin {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁.Perm l₂) {n : ℕ} (hn : l₁.length = n) :
    ∃ σ : Equiv.Perm (Fin n), ∀ (i : Fin n) (h₁ : (i : ℕ) < l₁.length) (h₂ : (σ i : ℕ) < l₂.length),
      l₂[(σ i : ℕ)] = l₁[(i : ℕ)] := by
  subst hn
  have hc : ∀ c, Fintype.card {i : Fin l₁.length // l₁.get i = c} =
      Fintype.card {i : Fin l₂.length // l₂.get i = c} := fun c => by
    rw [card_fiber, card_fiber, h.count_eq]
  let e : Fin l₁.length ≃ Fin l₂.length := Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c)
  have he : ∀ i, l₂.get (e i) = l₁.get i := Equiv.ofFiberEquiv_map _
  refine ⟨e.trans (finCongr h.length_eq.symm), fun i h₁ h₂ => ?_⟩
  simpa using he i

theorem length_toList {J : Type} (m : J →₀ ℕ) : (Finsupp.toMultiset m).toList.length = m.degree := by
  rw [Multiset.length_toList, Finsupp.card_toMultiset]
  simp only [Finsupp.sum, id]
  rfl

end RootMono


open RootMono in
theorem arMono_add_single (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem)
    (t : ℝ) (m : Ψ × Fin N →₀ ℕ) (r : Ψ × Fin N) (hII : IsIntersectionSystem II) (hm : m.degree = dimFl Ψ N) :
    M.arMono II t ((m + Finsupp.single r 1).mapDomain some) =
      II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r)) / (M.δ : ℝ) := by
  classical
  have hn : (m + Finsupp.single r 1).mapDomain some = m.mapDomain some + Finsupp.single (some r) 1 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hdm : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hdeg : ((m + Finsupp.single r 1).mapDomain some).degree = dimFl Ψ N + 1 := by
    rw [hn, map_add (f := _), hdm, Finsupp.degree_single]
  have hnone : ((m + Finsupp.single r 1).mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  have hperm : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.Perm
      ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList, hn, map_add (f := _)]
    simp
  have hlen₁ : (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length = dimFl Ψ N + 1 := by
    rw [length_toList, hdeg]
  have hlen₀ : (Finsupp.toMultiset (m.mapDomain some)).toList.length = dimFl Ψ N := by
    rw [length_toList, hdm]
  have hsm : ∀ o, IsSmoothHerm (M.line t o) := by
    intro o
    cases o with
    | none => exact M.A_smooth
    | some b => exact M.x_smooth t b
  set L : Fin (dimFl Ψ N + 1) → HermLine M.ι :=
    Fin.snoc (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) (M.x t r) with hL
  have hval : ∀ (j : Fin (dimFl Ψ N + 1))
      (hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length),
      L j = M.line t (((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[(j : ℕ)]) := by
    intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · intro hj
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.last (dimFl Ψ N) : Fin _) : ℕ)] = some r := by
        simp [List.getElem_append, hlen₀]
      rw [this, hL, Fin.snoc_last]
      rfl
    · intro hj
      have hk : (k : ℕ) < (Finsupp.toMultiset (m.mapDomain some)).toList.length := by
        rw [hlen₀]; exact k.2
      have : ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r])[((Fin.castSucc k : Fin _) : ℕ)] =
          (Finsupp.toMultiset (m.mapDomain some)).toList[(k : ℕ)] := by
        exact List.getElem_append_left hk
      rw [this, hL, Fin.snoc_castSucc]
      simp only [monoLines, dif_pos hk]
      rfl
  have hLs : ∀ j, IsSmoothHerm (L j) := by
    intro j
    have hj : (j : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, j.2]
    rw [hval j hj]
    exact hsm _
  obtain ⟨σ, hσ⟩ := exists_perm_fin hperm hlen₁
  have hfun : monoLines (M.line t) ((m + Finsupp.single r 1).mapDomain some) (dimFl Ψ N + 1) = L ∘ σ := by
    funext i
    have h₁ : (i : ℕ) < (Finsupp.toMultiset ((m + Finsupp.single r 1).mapDomain some)).toList.length := by
      rw [hlen₁]; exact i.2
    have h₂ : (σ i : ℕ) < ((Finsupp.toMultiset (m.mapDomain some)).toList ++ [some r]).length := by
      simp [hlen₀, (σ i).2]
    simp only [monoLines, dif_pos h₁, Function.comp, hval (σ i) h₂, hσ i h₁ h₂]
    rfl
  unfold RootModel.arMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one, hfun]
  congr 1
  exact (hII M.K M.ι).1 M.P (dimFl Ψ N + 1) L σ M.arith hLs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MonoLinesLineSmooth

section

@[expose] public section

noncomputable section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem line_smooth_at (M : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem line_a_eq (M : RootModel Ψ N) (t s : ℝ) (j : Option (Ψ × Fin N)) : (M.line t j).a = (M.line s j).a := by
  cases j with
  | none => rfl
  | some r => exact (M.x_deg t r).trans (M.x_deg s r).symm

theorem monoLines_line_smooth (M : RootModel Ψ N) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsSmoothHerm (monoLines (M.line t) m d k) := by
  unfold monoLines
  split_ifs with h
  · exact line_smooth_at M t _
  · exact contDiffOn_const

theorem monoLines_line_a (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (k : Fin d) :
    (monoLines (M.line t) m d k).a = (monoLines (M.line s) m d k).a := by
  unfold monoLines
  split_ifs with h
  · exact line_a_eq M t s _
  · rfl

theorem ptsIntegral_line_eq (hD : DegreeStatement) (M : RootModel Ψ N) (t s : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    ptsIntegral M.P (pot (monoLines (M.line t) m (dimFl Ψ N))) (fun _ => 1) =
      ptsIntegral M.P (pot (monoLines (M.line s) m (dimFl Ψ N))) (fun _ => 1) := by
  rw [hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M t m _) Nat.prime_two,
    hD M.K M.ι M.P (dimFl Ψ N) _ 2 M.arith (monoLines_line_smooth M s m _) Nat.prime_two]
  simp only [monoLines_line_a M t s m]

theorem geoMono_eq (hD : DegreeStatement) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ)
    (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N) :
    ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (fun _ => 1) / (M.δ : ℝ) =
      M.geoMono (m.mapDomain some) := by
  have hdeg : (m.mapDomain some).degree = dimFl Ψ N := by
    rw [Finsupp.degree_mapDomain, hm]
  have hnone : (m.mapDomain some) none = 0 :=
    Finsupp.mapDomain_notin_range _ _ (by simp)
  rw [ptsIntegral_line_eq hD M t 1]
  unfold RootModel.geoMono
  rw [if_pos hdeg, hnone, pow_zero, mul_one]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFun

section

@[expose] public section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.RootSum

theorem mono_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (t : ℝ)
    (m : Option (Ψ × Fin N) →₀ ℕ) (d : ℕ) (j : Fin d) : IsSmoothHerm (monoLines (M.line t) m d j) := by
  unfold monoLines
  split_ifs
  · rename_i h
    generalize (Finsupp.toMultiset m).toList.get ⟨j, h⟩ = o
    cases o with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  · unfold IsSmoothHerm
    simp only [trivLine]
    exact contDiffOn_const

theorem PP_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (m : Option (Ψ × Fin N) →₀ ℕ) :
    M.PP II (monomial m 1) = limUnder (𝓝[>] 0) fun t => M.arMono II t m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem geoFun_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)
    (m : Option (Ψ × Fin N) →₀ ℕ) : M.geoFun (monomial m 1) = M.geoMono m := by
  exact Module.Basis.constr_basis (basisMonomials (Option (Ψ × Fin N)) ℝ) ℝ _ m

theorem toA_pk_monomial {Ψ : Type} [Fintype Ψ] {N : ℕ} (τ : Ψ) (m : Ψ × Fin N →₀ ℕ) :
    toA (pk τ 1 * monomial m (1 : ℝ) : RP Ψ N) =
      ∑ i : Fin N, monomial ((m + Finsupp.single (τ, i) 1).mapDomain some) (1 : ℝ) := by

  rw [toA, pk, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one, X, monomial_mul, rename_monomial, add_comm, mul_one]

theorem sum_arMono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (m : Ψ × Fin N →₀ ℕ) (hm : m.degree = dimFl Ψ N)
    (t : ℝ) (ht : 0 < t) :
    ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some) =
      R.ht * M.geoMono (m.mapDomain some) -
        ptsIntegral M.P (pot (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N))) (R.v t) / (M.δ : ℝ) := by
  have h1 := GlobalTheory.T.intersection_family_multilinear hP hM M.K M.ι M.Ω R.F M.y R.φ (II M.K M.ι) M.P (dimFl Ψ N)
    (monoLines (M.line t) (m.mapDomain some) (dimFl Ψ N)) R.A R.S (dimFl Ψ N + 1) N
    (fun i => M.x t (τ, i)) (R.v t) (hII M.K M.ι) M.arith R.overInt le_rfl M.arith
    (mono_smooth M t _ _) R.A_smooth (fun i => M.x_smooth t _) (R.v_inv t) (R.v_smooth t)
    (by simp only [M.x_deg]; exact R.deg) (R.prod t ht)
  rw [Finset.sum_congr rfl fun i _ => arMono_add_single Ψ N M II t m (τ, i) hII hm, ← Finset.sum_div, h1,
    ← geoMono_eq hD Ψ N M t m hm, RootFlat.ht]
  ring

theorem PP_mono (hP : PtsIntegrableStatement) (hM : MetricLocalStatement) (hD : DegreeStatement)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ)
    (R : RootFlat M τ) (hII : IsIntersectionSystem II) (hC : M.Converges II) (m : Ψ × Fin N →₀ ℕ)
    (hm : m.degree = dimFl Ψ N) :
    M.PP II (toA (pk τ 1 * monomial m 1)) = R.ht * M.geoFun (toA (monomial m 1)) := by

  rw [toA_pk_monomial, map_sum, toA, rename_monomial, geoFun_monomial]
  simp only [PP_monomial]
  have h1 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (∑ i : Fin N, limUnder (𝓝[>] 0) fun t =>
        M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))) :=
    tendsto_finsetSum _ fun i _ => tendsto_nhds_limUnder (hC _)
  have h2 : Tendsto (fun t => ∑ i : Fin N, M.arMono II t ((m + Finsupp.single (τ, i) 1).mapDomain some))
      (𝓝[>] 0) (𝓝 (R.ht * M.geoMono (m.mapDomain some) - 0 / (M.δ : ℝ))) := by
    refine (tendsto_const_nhds.sub ((R.small m hm).div_const _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (sum_arMono hP hM hD M II τ R hII m hm t ht).symm
  rw [tendsto_nhds_unique h1 h2, zero_div, sub_zero]

end GlobalTheory.CompanionTheory.Ar.Flat.RootSum

open GlobalTheory.CompanionTheory.Ar.Flat.RootSum in
theorem GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  intro hP hM hD Ψ _ _ N M II τ R Q hII hC hQ
  have hQ' : Q = ∑ m ∈ Q.support, Q.coeff m • monomial m (1 : ℝ) := by
    conv_lhs => rw [Q.as_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have hA : ∀ (c : ℝ) (F : RP Ψ N), toA (c • F) = c • toA F := fun c F => map_smul (rename some) c F
  have hS : ∀ (s : Finset (Ψ × Fin N →₀ ℕ)) (F : _ → RP Ψ N), toA (∑ m ∈ s, F m) = ∑ m ∈ s, toA (F m) :=
    fun s F => map_sum (rename some) F s

  rw [hQ', Finset.mul_sum, hS, hS, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = dimFl Ψ N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hm)
  rw [mul_smul_comm, hA, hA, map_smul, map_smul, PP_mono hP hM hD M II τ R hII hC m hd, smul_eq_mul, smul_eq_mul]
  ring
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootFlatPushforwardGeoFunStatement

section

@[expose] public section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.root_flat_pushforward_geoFun : PtsIntegrableStatement → MetricLocalStatement → DegreeStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (II : IntersectionSystem) (τ : Ψ) (R : RootFlat M τ) (Q : RP Ψ N), IsIntersectionSystem II → M.Converges II → Q.IsHomogeneous (dimFl Ψ N) → M.PP II (toA (pk τ 1 * Q)) = R.ht * M.geoFun (toA Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.root_flat_pushforward_eq <;> assumption)
end
end
