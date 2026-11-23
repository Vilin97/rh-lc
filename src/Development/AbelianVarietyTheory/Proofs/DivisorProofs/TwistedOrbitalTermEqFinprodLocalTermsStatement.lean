module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForallStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIffStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProd

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AvgRestr

theorem apply_out_mk {G : Type} [Group G] (u : G → ℂ) (x : G) :
    u ((QuotientGroup.mk x : G ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  exact k.2 x

theorem avg_pi_comp {H : Type} [Group H] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (π : H →* ∀ i, G i) (hπ : Function.Surjective π) (u : ∀ i, G i → ℂ) (hu : ∀ i, (rStab (u i)).index ≠ 0) :
    avg (fun k => ∏ i, u i (π k i)) = ∏ i, avg (u i) := by
  set P : Subgroup (∀ i, G i) := Subgroup.pi Set.univ fun i => rStab (u i) with hP
  set R : Subgroup H := P.comap π with hRdef
  have hPi : P.index = ∏ i, (rStab (u i)).index := by
    simp_rw [hP, Subgroup.index, ← Nat.card_pi]
    refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
    rw [QuotientGroup.leftRel_pi]
  have hRi : R.index = ∏ i, (rStab (u i)).index := by
    rw [hRdef, Subgroup.index_comap_of_surjective _ hπ, hPi]
  have hR0 : R.index ≠ 0 := by rw [hRi]; exact Finset.prod_ne_zero_iff.2 fun i _ => hu i
  have hRle : R ≤ rStab (fun k => ∏ i, u i (π k i)) := by
    intro k hk x
    have hk' : ∀ i, π k i ∈ rStab (u i) := fun i => ((Subgroup.mem_pi _).1 hk) i (Set.mem_univ i)
    simp only [map_mul, Pi.mul_apply]
    exact Finset.prod_congr rfl fun i _ => hk' i (π x i)
  rw [avg_eq_of_le_rStab H _ R hRle hR0]
  haveI : R.FiniteIndex := ⟨hR0⟩
  haveI : ∀ i, (rStab (u i)).FiniteIndex := fun i => ⟨hu i⟩
  haveI : Fintype (H ⧸ R) := Fintype.ofFinite _
  haveI : ∀ i, Fintype (G i ⧸ rStab (u i)) := fun i => Fintype.ofFinite _
  let e : H ⧸ R → ∀ i, G i ⧸ rStab (u i) := fun q i => QuotientGroup.mk (π q.out i)
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      apply QuotientGroup.eq.2
      show π (q.out⁻¹ * q'.out) ∈ P
      refine (Subgroup.mem_pi _).2 fun i _ => ?_
      have := QuotientGroup.eq.1 (congrFun hq i)
      simpa [map_mul, map_inv] using this
    · intro x
      obtain ⟨k, hk⟩ := hπ fun i => (x i).out
      refine ⟨QuotientGroup.mk k, funext fun i => ?_⟩
      obtain ⟨r, hr⟩ := QuotientGroup.mk_out_eq_mul R k
      have hr' : π r ∈ P := r.2
      show (QuotientGroup.mk (π (QuotientGroup.mk k : H ⧸ R).out i) : G i ⧸ rStab (u i)) = x i
      rw [hr, map_mul, Pi.mul_apply, hk]
      conv_rhs => rw [← QuotientGroup.out_eq' (x i)]
      apply QuotientGroup.eq.2
      simpa using ((Subgroup.mem_pi _).1 hr') i (Set.mem_univ i)
  have hsum : ∑ᶠ q : H ⧸ R, ∏ i, u i (π q.out i) = ∏ i, ∑ᶠ q : G i ⧸ rStab (u i), u i q.out := by
    rw [finsum_eq_sum_of_fintype]
    simp_rw [finsum_eq_sum_of_fintype]
    rw [Fintype.prod_sum]
    exact Fintype.sum_bijective e he _ _ fun q => Finset.prod_congr rfl fun i _ => (apply_out_mk (u i) _).symm
  rw [hsum, hRi]
  simp only [avg]
  rw [Finset.prod_mul_distrib]
  push_cast
  rw [Finset.prod_inv_distrib]

end GlobalTheory.AvgRestr

namespace GlobalTheory.AvgRestr

theorem avg_restr_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)),
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ),
    (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) →
    avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      ∏ᶠ v, avg (u v) := by
  intro X V Y _ _ _ _ pf K hX u hu hev
  obtain ⟨S, hS⟩ := GlobalTheory.RestrMeas.exists_finset_of_eventually hev
  set Kg : Subgroup X := ⨅ v, (K v).comap (pf v) with hKg
  let π : Kg →* ∀ v : S, K v.1 := MonoidHom.pi fun v =>
    ((pf v.1).comp Kg.subtype).codRestrict (K v.1) fun k => Subgroup.mem_iInf.1 k.2 v.1
  have hπ : Function.Surjective π := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    have hz : ∀ v, z v ∈ K v := fun v => by
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z (Eventually.of_forall hz)
    have hxK : x ∈ Kg := Subgroup.mem_iInf.2 fun v => by
      show pf v x ∈ K v
      rw [hx v]; exact hz v
    refine ⟨⟨x, hxK⟩, funext fun v => Subtype.ext ?_⟩
    show pf v.1 x = (y v : Y v.1)
    rw [hx v.1]
    simp [z, v.2]
  have hF : (fun k : Kg => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) =
      fun k => ∏ v : S, u v.1 (π k v) := by
    funext k
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv (hS v h _),
      ← Finset.prod_coe_sort S]
    rfl
  have hA : ∏ᶠ v, avg (u v) = ∏ v : S, avg (u v.1) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) fun v hv => by_contra fun h => hv ?_,
      ← Finset.prod_coe_sort S]
    have hc : u v = fun _ => 1 := funext (hS v h)
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (fun _ : K v => (1 : ℂ)) (fun _ => 1) 1 1
      (by rw [← hc]; exact hu v) (by rw [← hc]; exact hu v)).2.2.2
  rw [hF, hA]
  exact avg_pi_comp π hπ (fun v : S => u v.1) fun v => hu v.1

end GlobalTheory.AvgRestr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupAverageRestrictedProductMaxCompactProdStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (u : ∀ v, K v → ℂ), (∀ v, (rStab (u v)).index ≠ 0) → (∀ᶠ v in cofinite, ∀ k, u v k = 1) → avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩) = ∏ᶠ v, avg (u v) := by
  first | exact @GlobalTheory.AvgRestr.avg_restr_prod | exact GlobalTheory.AvgRestr.avg_restr_prod | (intros; apply GlobalTheory.AvgRestr.avg_restr_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProd

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RelIdxRestr

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_iInf_comap {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)]
    [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v))
    (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (C H : ∀ v, Subgroup (Y v))
    (_hfin : ∀ v, (H v).relIndex (C v) ≠ 0) (hev : ∀ᶠ v in cofinite, C v ≤ H v) :
    (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  classical
  set S : Finset V := (Filter.eventually_cofinite.1 hev).toFinset with hS
  have hSm : ∀ v, v ∉ S → C v ≤ H v := fun v hv => by
    by_contra h; exact hv (by simpa [hS] using h)
  set Cg := ⨅ v, (C v).comap (pf v)
  set Hg := ⨅ v, (H v).comap (pf v)
  have hmemC : ∀ x : X, x ∈ Cg ↔ ∀ v, pf v x ∈ C v := fun x => by simp [Cg, Subgroup.mem_iInf]
  have hmemH : ∀ x : X, x ∈ Hg ↔ ∀ v, pf v x ∈ H v := fun x => by simp [Hg, Subgroup.mem_iInf]
  let φ : Cg →* ∀ v : S, C v := MonoidHom.pi fun v =>
    ((pf v).comp Cg.subtype).codRestrict (C v) fun x => (hmemC x).1 x.2 v
  have hφ : ∀ x (v : S), ((φ x v : C v) : Y v) = pf v x := fun _ _ => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    let z : ∀ v, Y v := fun v => if h : v ∈ S then (y ⟨v, h⟩ : Y v) else 1
    obtain ⟨x, -, hx⟩ := hX.exists_eq (fun w => w.elim) z
      (GlobalTheory.RestrMeas.eventually_of_finset S fun v hv => by simp [z, hv, one_mem])
    have hxC : x ∈ Cg := (hmemC x).2 fun v => by
      rw [hx v]
      by_cases h : v ∈ S
      · simp only [z, dif_pos h]; exact (y ⟨v, h⟩).2
      · simp only [z, dif_neg h]; exact one_mem _
    refine ⟨⟨x, hxC⟩, funext fun v => Subtype.ext ?_⟩
    rw [hφ]
    show pf v x = _
    rw [hx v]
    simp [z, v.2]
  have hcomap : Hg.subgroupOf Cg = (Subgroup.pi Set.univ fun v : S => (H v).subgroupOf (C v)).comap φ := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, hmemH]
    constructor
    · intro h v; exact h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h ⟨v, hv⟩
      · exact hSm v hv ((hmemC x).1 x.2 v)
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ,
    finprod_eq_prod_of_mulSupport_subset (s := S)]
  · exact (Finset.prod_coe_sort S fun v => (H v).relIndex (C v))
  · intro v hv
    by_contra h
    exact hv (Subgroup.relIndex_eq_one.2 (hSm v h))

end GlobalTheory.RelIdxRestr

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexRestrictedProductComponentwiseEqProdStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (C H : ∀ v, Subgroup (Y v)), (∀ v, (H v).relIndex (C v) ≠ 0) → (∀ᶠ v in cofinite, C v ≤ H v) → (⨅ v, (H v).comap (pf v)).relIndex (⨅ v, (C v).comap (pf v)) = ∏ᶠ v, (H v).relIndex (C v) := by
  first | exact @GlobalTheory.RelIdxRestr.relIndex_iInf_comap | exact GlobalTheory.RelIdxRestr.relIndex_iInf_comap | (intros; apply GlobalTheory.RelIdxRestr.relIndex_iInf_comap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTerms

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

open GlobalTheory.BCT

theorem mem_map_conj_iff_term {G : Type} [Group G] (K : Subgroup G) (y z : G) :
    z ∈ K.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * z * y ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem cptPart_le_self_term {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T :=
  Subgroup.closure_le _ |>.mpr fun _ ht => ht.1

theorem inf_relIndex_of_le_left_term {G : Type} [Group G] {A B C : Subgroup G} (h : C ≤ A) :
    (A ⊓ B).relIndex C = B.relIndex C := by
  unfold Subgroup.relIndex
  congr 1
  ext ⟨c, hc⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact and_iff_right (h hc)

theorem avg_eq_one_of_forall_term {H : Type} [Group H] (u : H → ℂ) (hu : ∀ k, u k = 1) : avg u = 1 := by
  have hs : rStab u = ⊤ := by
    ext k; simp only [Subgroup.mem_top, iff_true]; intro x; rw [hu, hu]
  have hi : (rStab u).index = 1 := Subgroup.index_eq_one.2 hs
  have hsub : Subsingleton (H ⧸ rStab u) := by
    have hc : Nat.card (H ⧸ rStab u) = 1 := hi
    exact (Nat.card_eq_one_iff_unique.1 hc).1
  unfold avg
  rw [hi, finsum_eq_single _ (QuotientGroup.mk 1 : H ⧸ rStab u) (fun q hq => absurd (Subsingleton.elim q _) hq), hu]
  simp

theorem twTerm_eq_finprod : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX θ θv hθ hK δ f fv hf hcomm hstab hwt hev x
  have hT : ∀ y, y ∈ twCent θ δ ↔ ∀ v, pf v y ∈ twCent (θv v) (pf v δ) := fun y => GlobalTheory.T.mem_twistedCentralizer_restrictedProduct_iff pf K hX θ θv hθ δ y
  have hC : ∀ y, y ∈ cptPart (twCent θ δ) ↔ ∀ v, pf v y ∈ cptPart (twCent (θv v) (pf v δ)) :=
    GlobalTheory.T.mem_compactPart_restrictedProduct_iff_forall pf K hX (twCent θ δ) (fun v => twCent (θv v) (pf v δ)) hT hcomm
  have hgood := hev.and (hX.eventually_mem x)
  have hCg : cptPart (twCent θ δ) = ⨅ v, (cptPart (twCent (θv v) (pf v δ))).comap (pf v) := by
    ext y; rw [hC, Subgroup.mem_iInf]; rfl
  have hHg : (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom =
      ⨅ v, ((K v).map (MulAut.conj (pf v x)).toMonoidHom).comap (pf v) := by
    ext y
    simp only [mem_map_conj_iff_term, Subgroup.mem_iInf, Subgroup.mem_comap, map_mul, map_inv]
  have hloc : ∀ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) = ((K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := fun v => inf_relIndex_of_le_left_term (cptPart_le_self_term _)
  have hCH : ∀ᶠ v in cofinite, cptPart (twCent (θv v) (pf v δ)) ≤ (K v).map (MulAut.conj (pf v x)).toMonoidHom :=
    hgood.mono fun v hv c hc => by
      rw [mem_map_conj_iff_term]
      exact mul_mem (mul_mem (inv_mem hv.2) (hv.1.2.2 hc)) hv.2
  have hrel : (twCent θ δ ⊓ (⨅ v, (K v).comap (pf v)).map (MulAut.conj x).toMonoidHom).relIndex
      (cptPart (twCent θ δ)) = ∏ᶠ v, (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) := by
    rw [inf_relIndex_of_le_left_term (cptPart_le_self_term _), hHg, hCg]
    simp only [hloc]
    exact GlobalTheory.T.relIndex_restrictedProduct_componentwise_eq_prod pf K hX (fun v => cptPart (twCent (θv v) (pf v δ)))
      (fun v => (K v).map (MulAut.conj (pf v x)).toMonoidHom)
      (fun v => by rw [← hloc]; exact (hwt v (pf v x)).2) hCH
  let u : ∀ v, K v → ℂ := fun v k => fv v ((pf v x * k)⁻¹ * pf v δ * θv v (pf v x * k))
  have hfun : (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => ∏ᶠ v, u v ⟨pf v k, Subgroup.mem_iInf.1 k.2 v⟩ := by
    funext k; rw [hf]; congr 1; funext v; simp only [u, map_mul, map_inv, hθ]
  have hu1 : ∀ᶠ v in cofinite, ∀ k, u v k = 1 := hgood.mono fun v hv k => by
    have hk : pf v x * (k : Y v) ∈ K v := mul_mem hv.2 k.2
    simp only [u]
    rw [hv.1.1, Set.indicator_of_mem (show _ ∈ (K v : Set (Y v)) from
      mul_mem (mul_mem (inv_mem hk) hv.1.2.1) (hK v _ hk))]
    rfl
  have havg : avg (fun k : (⨅ v, (K v).comap (pf v) : Subgroup X) => f ((x * k)⁻¹ * δ * θ (x * k))) =
      ∏ᶠ v, avg (u v) := by
    rw [hfun]; exact GlobalTheory.T.groupAverage_restrictedProduct_maxCompact_prod pf K hX u (fun v => hstab v (pf v x)) hu1
  have hfa : Function.HasFiniteMulSupport fun v => (((twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj (pf v x)).toMonoidHom).relIndex
      (cptPart (twCent (θv v) (pf v δ))) : ℕ) : ℂ) :=
    (eventually_cofinite.1 hCH).subset fun v hv h => hv (by
      show ((_ : ℕ) : ℂ) = 1
      rw [hloc, Subgroup.relIndex_eq_one.2 h, Nat.cast_one])
  have hfb : Function.HasFiniteMulSupport fun v => avg (u v) :=
    (eventually_cofinite.1 hu1).subset fun v hv h => hv (avg_eq_one_of_forall_term _ h)
  unfold twTerm
  rw [hrel, havg, Nat.cast_finprod', ← finprod_mul_distrib hfa hfb]

end GlobalTheory.EulerAbs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalTermEqFinprodLocalTermsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.twistedOrbitalTerm_eq_finprod_localTerms : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → (∀ v, ∀ k ∈ K v, θv v k ∈ K v) → ∀ (δ : X) (f : X → ℂ) (fv : ∀ v, Y v → ℂ), (∀ x, f x = ∏ᶠ v, fv v (pf v x)) → (∀ v, ∀ a ∈ twCent (θv v) (pf v δ), ∀ b ∈ twCent (θv v) (pf v δ), a * b = b * a) → (∀ v (y : Y v), (rStab fun k : K v => fv v ((y * k)⁻¹ * pf v δ * θv v (y * k))).index ≠ 0) → (∀ v (y : Y v), twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (θv v) (pf v δ)) ∧ (twCent (θv v) (pf v δ) ⊓ (K v).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (θv v) (pf v δ))) ≠ 0) → (∀ᶠ v in cofinite, fv v = (K v : Set (Y v)).indicator 1 ∧ pf v δ ∈ K v ∧ cptPart (twCent (θv v) (pf v δ)) ≤ K v) → ∀ x, GlobalTheory.EulerAbs.twTerm θ (⨅ v, (K v).comap (pf v)) δ f x = ∏ᶠ v, GlobalTheory.EulerAbs.twTerm (θv v) (K v) (pf v δ) (fv v) (pf v x) := by
  first | exact @GlobalTheory.EulerAbs.twTerm_eq_finprod | exact GlobalTheory.EulerAbs.twTerm_eq_finprod | (intros; apply GlobalTheory.EulerAbs.twTerm_eq_finprod <;> assumption)
end
end
