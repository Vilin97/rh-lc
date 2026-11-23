module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DvdOfCompl
import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestrictedWeightFirstTwoEq
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.IsMultiHom
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DgFalseDiag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GroupLattices.FockModels.MkP
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RankMulConductorDivLeOne
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ThAllMonomial

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv)

abbrev Aset (k d : ℕ) := {α : Fin k →₀ ℕ // ∑ c, α c = d}

instance Aset_finite (k d : ℕ) : Finite (Aset k d) := by
  have : ({α : Fin k →₀ ℕ | ∑ c, α c = d}).Finite := by
    refine (Finset.finite_toSet (Finset.univ.finsuppAntidiag d)).subset ?_
    intro α hα
    simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    exact ⟨hα, Finset.subset_univ _⟩
  exact this.to_subtype

theorem XsFinP (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : (Xs m top vec ν).Finite :=
  (sSIdxFinite (m + 1) (m + 1) ν).subset fun _ he => he.1

instance XsFinP' (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Finite (Xs m top vec ν) :=
  (XsFinP m top vec ν).to_subtype

def glue {n' k : ℕ} {d : Fin n' → ℕ} (a : ∀ s, Aset k (d s)) : Fin n' × Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (a v.1).1 v.2

theorem expand {R : Type} [CommRing R] {n' k : ℕ} {d : Fin n' → ℕ} [Fintype (∀ s, Aset k (d s))]
    (Q : MvPolynomial (Fin n' × Fin k) R) (hQ : IsMultiHom d Q) :
    Q = ∑ a : (∀ s, Aset k (d s)), monomial (glue a) (AddMonoidAlgebra.coeff Q (glue a)) := by
  classical
  ext e
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases he : e ∈ Q.support
  · let a : ∀ s, Aset k (d s) := fun s =>
      ⟨Finsupp.equivFunOnFinite.symm fun c => e (s, c), by simpa using hQ e he s⟩
    have ha : glue a = e := by
      ext v
      rfl
    rw [Finset.sum_eq_single a]
    · rw [if_pos ha, ha]
    · intro a' _ hne
      rw [if_neg]
      intro h
      apply hne
      funext s
      apply Subtype.ext
      ext c
      have := DFunLike.congr_fun (h.trans ha.symm) (s, c)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : AddMonoidAlgebra.coeff Q e = 0 := by simpa using he
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [h, h0]
    · rfl

theorem thAll_monomial (F : Type) [CommRing F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ)
    (a : ∀ s, Aset (m + 1) (d s)) (r : F) :
    thAll F n' m vec (monomial (glue a) r) = r • ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
  unfold thAll
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Algebra.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_pow]
  rfl

section Core

variable (F : Type) [Field F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ) {X : Fin n' → Type}
  (b : ∀ s, X s → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F)

def famG (z : (∀ s, Aset (m + 1) (d s)) × (∀ s, X s)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) F :=
  ∏ s, blockEmb F s ((∏ c, Nv F m (vec s) c ^ ((z.1 s).1 c)) * b s (z.2 s))

def fam1 (s : Fin n') (y : Aset (m + 1) (d s) × X s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F :=
  (∏ c, Nv F m (vec s) c ^ (y.1.1 c)) * b s y.2

def pairUp {n' : ℕ} {A X : Fin n' → Type} (z : (∀ s, A s) × (∀ s, X s)) : ∀ s, A s × X s := fun s => (z.1 s, z.2 s)

theorem pairUp_inj {n' : ℕ} {A X : Fin n' → Type} : Function.Injective (pairUp (A := A) (X := X)) := by
  intro z z' h
  refine Prod.ext ?_ ?_
  · funext s
    exact congrArg Prod.fst (congrFun h s)
  · funext s
    exact congrArg Prod.snd (congrFun h s)

theorem famG_li (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s)) :
    LinearIndependent F (famG F n' m vec d b) := by
  have hli : LinearIndependent F (fun i : (∀ s, Aset (m + 1) (d s) × X s) =>
      ∏ s, blockEmb F s (fam1 F n' m vec d b s (i s))) :=
    ldtensor_prod_linInd_field F (fam1 F n' m vec d b) hpos
  have h2 := hli.comp (pairUp (A := fun s => Aset (m + 1) (d s)) (X := X)) pairUp_inj
  exact h2

theorem famG_sum [Fintype (∀ s, Aset (m + 1) (d s))] (Q : MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : IsMultiHom d Q)
    (i : ∀ s, X s) :
    (∑ a : (∀ s, Aset (m + 1) (d s)), AddMonoidAlgebra.coeff Q (glue a) • famG F n' m vec d b (a, i)) =
      thAll F n' m vec Q * ∏ s, blockEmb F s (b s (i s)) := by
  have e := expand Q hQ
  have e2 : thAll F n' m vec Q =
      ∑ a : (∀ s, Aset (m + 1) (d s)), AddMonoidAlgebra.coeff Q (glue a) •
        ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
    conv_lhs => rw [e]

    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => thAll_monomial F n' m vec d a _
  rw [e2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  unfold famG
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul]

theorem big_core [∀ s, Finite (X s)] (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s))
    (J : Finset (∀ s, X s)) (Q : (∀ s, X s) → MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : ∀ i, IsMultiHom d (Q i))
    (hsum : ∑ i ∈ J, thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) = 0) : ∀ i ∈ J, Q i = 0 := by
  classical
  have : Fintype (∀ s, Aset (m + 1) (d s)) := Fintype.ofFinite _
  have : Fintype (∀ s, X s) := Fintype.ofFinite _
  have hli2 := famG_li F n' m vec d b hpos
  rw [Fintype.linearIndependent_iff] at hli2
  have key := hli2 (fun z => if z.2 ∈ J then AddMonoidAlgebra.coeff (Q z.2) (glue z.1) else 0) ?_
  · intro i hi
    rw [expand (Q i) (hQ i)]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h1 := key (a, i)
    simp only [hi, if_true] at h1
    rw [h1, monomial_zero]
  · rw [Fintype.sum_prod_type_right, ← hsum]
    have h1 : ∀ i : (∀ s, X s),
        (∑ a : (∀ s, Aset (m + 1) (d s)), (if i ∈ J then AddMonoidAlgebra.coeff (Q i) (glue a) else 0) • famG F n' m vec d b (a, i)) =
        if i ∈ J then thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) else 0 := by
      intro i
      by_cases hi : i ∈ J
      · simp only [hi, if_true]
        exact famG_sum F n' m vec d b (Q i) (hQ i) i
      · simp only [hi, if_false, zero_smul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_ite_mem, Finset.univ_inter]

end Core

theorem bigInd : BigInd := by
  intro F _ n' m hm top vec d ν htop hν b hb J Q hQ hsum
  exact big_core F n' m vec d b
    (fun s => posInd F m hm (top s) (vec s) (d s) (ν s) (htop s) (hν s) (b s) (hb s)) J Q hQ hsum

end Formalism.MainNotions.TestSideCounting
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TheoremIIClosedOfTestBound

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)


set_option maxHeartbeats 1600000 in
theorem primStep_of (hTr : TransStep) (hSub : SubstPol) (C CLa : ℝ) (hSP : SPStep C) : PrimStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hm2 : 2 ≤ m := by omega
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hwirr : Irreducible w := hSet.2.1
  set ν : Fin n' → Fin (m + 1) → ℕ := fun s => nuOf (lamAt (restW TT lam0) s) with hν
  set top : Fin n' → Bool := fun s => decide (s ∈ TT) with htop
  let I := ∀ s : Fin n', Xs m (top s) (vecE n' s) (ν s)
  have : Finite I := Pi.finite
  let _ : Fintype I := Fintype.ofFinite I
  let eI : I ≃ Fin (Nat.card I) := Finite.equivFin I
  have hbas := fun s => sSBasis O (m + 1) (m + 1) (ν s)
  choose b hb1 hb2 using hbas
  let bX : ∀ s, Xs m (top s) (vecE n' s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) O :=
    fun s y => b s ⟨y.1, y.2.1⟩
  let sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O := fun i => ∏ s, blockEmb O s (bX s (i s))
  have hsO : ∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt (restW TT lam0) s))) := by
    intro i
    refine Submodule.subset_span ⟨fun s => bX s (i s), fun s => ?_, rfl⟩
    show bX s (i s) ∈ dualWeyl O (m + 1) (m + 1) (ν s)
    rw [← (hb1 s).2.1]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨sh', hsh, hmain⟩ := hTr p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm2 (by omega) (by omega) (dT TT lam0)
    (restW TT lam0) lam0 (lambda_zero_eq_product TT lam0) (restW_dom (by omega) TT lam0 hdom) e he hm g hhm hg hbasis Θ hΘ I sO hsO
  refine ⟨Nat.card I, fun i => sh' (eI.symm i), fun i => hsh _, card_all hm2 TT lam0 hdom, ?_⟩
  intro S hS c hcu hmem
  obtain ⟨x0, hx0⟩ := hcu
  obtain ⟨SPO, hSPO1, hSPO2⟩ := hSP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    hrk F hF g hg (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)
  let P : I → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) :=
    fun i => ∑ bb, c (bb, eI i) • FsB bb
  let T0 : I → RRing O n' (r + K) := fun i => ∑ bb, c (bb, eI i) • B bb
  let Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O := fun i => rename (castV hk) (T0 i) * SPO
  have hPQ : ∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) =
      map (algebraMap O (KK O)) (Q i) := by
    intro i
    have e1 : ((P i : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
        MvPolynomial (TV n' (m + 1)) (KK O)) =
        ∑ bb, algebraMap O (KK O) (c (bb, eI i)) • (FsB bb : MvPolynomial (TV n' (m + 1)) (KK O)) := by
      simp only [P, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, hFsB, symB, toK, Q, T0, map_mul, map_sum, ← hSPO1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun bb _ => ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_C, mul_assoc]
  have hv : (((∑ y, c y • S y : Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      ∑ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
        ((sh' i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
    have e2 : ∀ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ∑ bb, c (bb, eI i) • ((Θ (FsB bb) : Vsp Kf (flW (m := m) (dT TT lam0))) :
          MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    simp only [e2, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Equiv.sum_comp eI]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [hS bb (eI i)]
    simp only [Equiv.symm_apply_apply, smul_mul_assoc]
  obtain ⟨R, hR⟩ := hmain P Q hPQ _ hv hmem

  let Fr := IsLocalRing.ResidueField O
  let res : O →+* Fr := IsLocalRing.residue O
  have hresw : res w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hwirr.not_isUnit
  have h0 : ∑ i ∈ (Finset.univ : Finset I), thAll Fr n' m (vecE n') (map res (Q i)) *
      ∏ s, blockEmb Fr s (map res (bX s (i s))) = 0 := by
    have h1 := congrArg (map res) hR
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_thAll, map_C, hresw, C_0, zero_mul, sO, map_prod, blockEmb, map_rename] at h1
    simpa only [blockEmb] using h1
  have hQhom : ∀ i, IsMultiHom (dT TT lam0) (map res (Q i)) := by
    intro i ee hee s
    have h1 : ee ∈ (Q i).support := support_map_subset res (Q i) hee
    have h2 : ee ∈ (map (algebraMap O (KK O)) (Q i)).support := by
      rw [support_map_of_injective _ (IsFractionRing.injective O (KK O))]
      exact h1
    rw [← hPQ i] at h2
    have h3 := hSub p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ (P i).2
    exact (Formalism.L2.G.Model.mem_Pol.1 h3) ee h2 s
  have hQ0 := bigInd Fr n' m hm2 top (vecE n') (dT TT lam0) ν
    (fun s hs => by
      have : s ∉ TT := by simpa [htop] using hs
      simp [dT, this])
    (fun s hs hv t ht => nu_odd (by omega) TT lam0 hdom s (by simpa [htop] using hs) hv t ht)
    (fun s y => map res (bX s y))
    (fun s y => by
      obtain ⟨d1, d2, -⟩ := hb2 s ⟨y.1, y.2.1⟩
      have := deg_map (colLex (m + 1) (m + 1)) res (bX s y) d2
      exact ⟨this.1.trans d1, this.2⟩)
    Finset.univ (fun i => map res (Q i)) hQhom h0
  have hq := hQ0 (eI.symm x0.2) (Finset.mem_univ _)
  simp only [Q, map_mul] at hq
  have hT : map res (rename (castV hk) (T0 (eI.symm x0.2))) = 0 := by
    rcases mul_eq_zero.1 hq with h1 | h1
    · exact h1
    · exact absurd h1 hSPO2
  rw [map_rename] at hT
  have hinj : Function.Injective (castV (n' := n') hk) := by
    intro u v huv
    simp only [castV, Prod.mk.injEq] at huv
    exact Prod.ext huv.1 (Fin.cast_injective _ huv.2)
  have hT' : map res (T0 (eI.symm x0.2)) = 0 := by
    apply rename_injective _ hinj
    rw [hT, map_zero]
  have hdvd : MvPolynomial.C w ∣ T0 (eI.symm x0.2) := by
    rw [C_dvd_iff_dvd_coeff]
    intro ee
    have h1 : res (AddMonoidAlgebra.coeff (T0 (eI.symm x0.2)) ee) = 0 := by
      simp only [← coeff_map, hT', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, hwirr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨y, hy⟩ := hdvd
  obtain ⟨T, hTc⟩ := hc
  have hfin := dvd_of_compl B hli T hTc w (fun bb => c (bb, x0.2)) y (by
    have : T0 (eI.symm x0.2) = ∑ bb, c (bb, x0.2) • B bb := by
      simp only [T0, Equiv.apply_symm_apply]
    rw [← this, hy, MvPolynomial.smul_eq_C_mul]) x0.1
  exact hwirr.not_isUnit (isUnit_of_dvd_unit hfin hx0)

theorem source_integrality_of_substitution (hTr : TransStep) (hSub : SubstPol) (C₀ : ℝ) (hC0 : 0 < C₀) (hSP : ∀ C, C₀ ≤ C → SPStep C)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  fun _ => ⟨C₀, hC0, fun C hC => primStep_of hTr hSub C CLa (hSP C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end
end
