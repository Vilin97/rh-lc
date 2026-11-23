module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.IsClosedGzS
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.LocChi
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
public import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity
public import GroundTheory.AutomorphicForms.WhittakerDistribution
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.ExistsClopenSep
import GroundTheory.AutomorphicForms.GLnLocal
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.TraceForm
import Mathlib.NumberTheory.LocalField.Basic
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.SymmetricIndices.IndexSym
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceFormCore

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.ContinuousCp

section

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def cp (x : Matrix (Fin n) (Fin n) k) : Fin (n + 1) → k := fun i => x.charpoly.coeff i

theorem continuous_cp : Continuous (cp : Matrix (Fin n) (Fin n) k → _) :=
  continuous_pi fun i => GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype (i : ℕ)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem cp_conj (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : cp (g.val * x * g⁻¹.val) = cp x := by
  funext i
  simp only [cp]
  rw [charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def poly (y : Fin (n + 1) → k) : k[X] := ∑ i : Fin (n + 1), C (y i) * X ^ (i : ℕ)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem cp_eq_iff (x : Matrix (Fin n) (Fin n) k) (y : Fin (n + 1) → k) : cp x = y ↔ x.charpoly = poly y := by
  constructor
  · rintro rfl
    have h := as_sum_range' x.charpoly (n + 1) (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)
    rw [h, poly, ← Fin.sum_univ_eq_sum_range (fun i => (monomial i) (x.charpoly.coeff i)) (n + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← C_mul_X_pow_eq_monomial]
    rfl
  · intro h
    funext i
    simp only [cp, h, poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun e => hj (Fin.ext e.symm)), mul_zero]) (by simp)]
    simp

theorem locChi_pf : PositivityTheory.RgUd.TP.Loc.LocChi k := by
  intro n Z U hU hfib ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  let p : Sp k n → _ := fun q => cp q.1
  have hp : Continuous p := continuous_cp.comp continuous_fst
  have hpact : ∀ g ∈ Gz Z, ∀ q, p (act g q) = p q := fun g _ q => cp_conj g q.1
  let C : Set (Sp k n) := Bz Z ×ˢ univ
  have hC : IsClosed C := (PositivityTheory.RgUd.T.LocStepPf.isClosed_Bz Z).prod isClosed_univ
  let W : Submodule ℂ (Sp k n → ℂ) :=
    { carrier := {w | ∀ V, IsClopen V → ξ (fun x => (p ⁻¹' V).indicator 1 x * w x) = 0}
      add_mem' := fun {a b} ha hb V hV => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (a + b) x) =
            (fun x => (p ⁻¹' V).indicator 1 x * a x) + (fun x => (p ⁻¹' V).indicator 1 x * b x) := by
          funext x
          simp [mul_add]
        rw [e, map_add (f := _), ha V hV, hb V hV, add_zero]
      zero_mem' := fun V _ => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (0 : Sp k n → ℂ) x) = 0 := by
          funext x
          simp
        rw [e, map_zero]
      smul_mem' := fun c a ha V hV => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (c • a) x) =
            c • (fun x => (p ⁻¹' V).indicator 1 x * a x) := by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, map_smul, ha V hV, smul_zero] }
  intro g hg
  have key : g ∈ W := by
    refine mem_of_forall_fiber (U := univ) hC hp ?_ ?_ (supportedIn_mono (subset_univ _) hg) ?_
    · rintro w ⟨hw1, hw2⟩ V hV
      refine hS _ (indicator_mul_mem (hV.preimage hp) hw1) fun q hq => ?_
      simp [(mem_vanishingOn.1 hw2) q hq]
    · intro V hV w hw V' hV'
      have := hw (V' ∩ V) (hV'.inter hV)
      convert this using 2
      funext x
      by_cases h1 : p x ∈ V' <;> by_cases h2 : p x ∈ V <;>
        simp [h1, h2]
    · intro y
      let N : Submodule ℂ (Sp k n → ℂ) := Submodule.span ℂ
        {h | ∃ γ ∈ Gz Z, ∃ f ∈ supportedIn (univ : Set (Sp k n)), h = (fun q => f (act γ q)) - f}
      have hmem : g ∈ N ⊔ (supportedIn univ ⊓ vanishingOn (C ∩ p ⁻¹' {y})) := by
        by_contra hn
        obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_notMem hn
        refine hf0 (hfib (poly y) f ?_ ?_ g hg)
        · intro u hu hu0
          refine hle (Submodule.mem_sup_right ⟨hu, fun q hq => hu0 q ⟨⟨hq.1.1, ?_⟩, trivial⟩⟩)
          exact (cp_eq_iff q.1 y).1 hq.2
        · intro γ hγ u hu
          have h1 : (fun q => u (act γ q)) - u ∈ N := Submodule.subset_span ⟨γ, hγ, u, hu, rfl⟩
          have h3 := hle (Submodule.mem_sup_left h1)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h3
          exact h3
      have hNW : N ≤ W := by
        rw [Submodule.span_le]
        rintro _ ⟨γ, hγ, u, hu, rfl⟩ V hV
        have hu' := indicator_mul_mem (hV.preimage hp) hu
        have h3 := hI γ hγ _ hu'
        rw [← sub_eq_zero, ← map_sub] at h3
        convert h3 using 2
        funext q
        have e : p (act γ q) = p q := hpact γ hγ q
        by_cases h1 : p q ∈ V <;> simp [h1, e]
      exact sup_le_sup_right hNW _ hmem
  have := key univ isClopen_univ
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Psplit
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Psplit

section

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fib_split (hSp : PositivityTheory.RgUd.TP.Loc.Split k) {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (χ : k[X]) {m : ℕ}
    (F : Fin m → Set (Matrix (Fin n) (Fin n) k)) (hF : IsPieces Z χ F) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hS : Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ univ)) (hI : Inv Z ξ) :
    ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ univ) ∧ Inv Z (η i)) ∧
      ∀ f ∈ supportedIn (univ : Set (Sp k n)), ξ f = ∑ i, η i f := by
  refine hSp n Z F (fun i => ⟨(hF.1 i).1, (hF.1 i).2.2⟩) hF.2.1 ξ ?_ hI
  intro f hf h0
  refine hS f hf fun p hp => ?_
  obtain ⟨i, hi⟩ := hF.2.2 p.1 hp.1.1 hp.1.2
  exact h0 p ⟨mem_iUnion.2 ⟨i, hi⟩, mem_univ _⟩

theorem locAll_of_pf : PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocAll k := by
  intro hSp hLC n Z _hZ hP ξ hS hI
  have hU : IsOpen {p : Sp k n | p.2 ≠ 0} := (isClosed_eq continuous_snd continuous_const).isOpen_compl
  refine hLC n Z _ hU (fun χ ξ' hS' hI' f hf => ?_) ξ hS hI
  obtain ⟨m, F, hF, hi⟩ := hP χ
  obtain ⟨η, hη, hsum⟩ := fib_split hSp Z χ F hF ξ' hS' hI'
  rw [hsum f (supportedIn_mono (subset_univ _) hf)]
  exact Finset.sum_eq_zero fun i _ => hi i (η i) (hη i).1 (hη i).2 f hf

theorem locOff_of_pf : PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocOff k := by
  intro hSp hLC n Z _hZ hP ξ hS hI U hU hUp
  refine hLC n Z U hU (fun χ ξ' hS' hI' f hf => ?_) ξ hS hI
  obtain ⟨m, F, hF, hi⟩ := hP χ
  obtain ⟨η, hη, hsum⟩ := fib_split hSp Z χ F hF ξ' hS' hI'
  rw [hsum f (supportedIn_mono (subset_univ _) hf)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases hi i with ⟨c, hc, hnil⟩ | hv
  · refine (hη i).1 f (supportedIn_mono (subset_univ _) hf) fun p hp => ?_
    by_contra h0
    exact ((hUp p (hf.2 h0)).2) ⟨⟨c, hc, hnil p.1 hp.1⟩, (hF.1 i).2.1 hp.1⟩
  · exact hv (η i) (hη i).1 (hη i).2 f (supportedIn_mono (fun p hp => (hUp p hp).1) hf)

theorem split (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k := split_pf
theorem locChi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.LocChi k := locChi_pf
theorem locOff_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocOff k := locOff_of_pf
theorem locAll_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocAll k := locAll_of_pf

end PositivityTheory.RgUd.TP.Loc.Psplit
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Ptransl

section

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc.Ptransl

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 - c, p.2)
  invFun p := (p.1 + c, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.sub continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.add continuous_const).prodMk continuous_snd

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem comp_mem {U V : Set (Sp k n)} (e : Sp k n ≃ₜ Sp k n) (hUV : ∀ p, e p ∈ U → p ∈ V) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn U) : (fun p => f (e p)) ∈ supportedIn V := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact hUV p (hsupp hp)

theorem act_trH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {g : GL (Fin n) k} (hg : g ∈ Gz Z) (p : Sp k n) : act g (trH c p) = trH c (act g p) := by
  have hcomm : c * (g : Matrix (Fin n) (Fin n) k) = g * c := hg c hc
  have hconj : (g : Matrix (Fin n) (Fin n) k) * c * (g⁻¹ : GL (Fin n) k) = c := by
    rw [← hcomm, Matrix.mul_assoc]
    simp
  simp only [act, trH, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Prod.mk.injEq, and_true]
  rw [Matrix.mul_sub, Matrix.sub_mul, hconj]

theorem transl : Transl k := by
  intro m Z hCR hNB c hc F hF hnil ξ hsupp hinv
  let ξ' : (Sp k m → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (trH c))
  have hξ' : ∀ f, ξ' f = ξ (fun p => f (trH c p)) := fun f => rfl
  have hmem : ∀ f ∈ supportedIn (Set.univ : Set (Sp k m)),
      (fun p => f (trH c p)) ∈ supportedIn (Set.univ : Set (Sp k m)) :=
    fun f hf => comp_mem (trH c) (fun _ _ => Set.mem_univ _) hf
  have hS : Supp ξ' (NB Z ×ˢ Set.univ) := by
    intro f hf hz
    rw [hξ']
    refine hsupp _ (hmem f hf) ?_
    rintro ⟨x, v⟩ ⟨hx, -⟩
    apply hz
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · intro a ha
      have h1 : a * x = x * a := hF hx a ha
      have h2 : a * c = c * a := hCR.1 a ha c hc
      change a * (x - c) = (x - c) * a
      rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    · exact hnil x hx
  have hI : T.Inv Z ξ' := by
    intro g hg f hf
    rw [hξ', hξ']
    have : (fun p => f (act g (trH c p))) = (fun p => (fun q => f (trH c q)) (act g p)) := by
      funext p
      rw [act_trH hc hg]
    rw [this]
    exact hinv g hg _ (hmem f hf)
  have hK := hNB ξ' hS hI
  intro f hf
  have hf' : (fun p => f ((trH c).symm p)) ∈ supportedIn {p : Sp k m | p.2 ≠ 0} :=
    comp_mem (trH c).symm (fun _ h => h) hf
  have := hK _ hf'
  rw [hξ'] at this
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Ptransl
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceForm

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Loc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem traceForm : TraceForm k := PositivityTheory.RgUd.TP.Loc.Ptf.traceForm k
theorem unimod : TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := PositivityTheory.RgUd.TP.Loc.Uni.unimod k
theorem locOff : LocOff k := PositivityTheory.RgUd.TP.Loc.Psplit.locOff_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)
theorem locAll : LocAll k := PositivityTheory.RgUd.TP.Loc.Psplit.locAll_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)
theorem transl : Transl k := PositivityTheory.RgUd.TP.Loc.Ptransl.transl

end PositivityTheory.RgUd.TP.Loc.Final
end
end
