module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroup
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.GlobalFields.TateThesis.AdelicChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCellFiniteUnionLocalDoubleCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffsStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittakerStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolic

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.CutProd

open GlobalTheory.JSW.Cut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

theorem lr_loc_of_mem_mirS {S : Finset (HeightOneSpectrum (𝓞 E))} {p : GA E (m + 1)} (hp : p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m))
    (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) = GlobalTheory.JSW.KirFin.lr 1 := by
  funext j
  have h := hp.2 j
  simp only [GlobalTheory.JSW.KirFin.lr]
  show ((pLoc E w).comp (pFin E)) ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
  rw [h]
  split_ifs with hj <;> simp [hj, Matrix.one_apply, eq_comm]

theorem exists_cut_prod (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ)
    (hψ : ∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) (K : Subgroup (GL (Fin (m + 1)) (Af E)))
    (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E)))
    (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) →
    (∀ w ∈ S, Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) →
    ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧
      ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
        (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) →
        ∀ y : GA E (m + 1), (∀ w ∈ S, GlobalTheory.JSW.KirFin.lr (GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y) =
          GlobalTheory.JSW.KirFin.lr 1) →
        GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    refine ⟨Finsupp.single 1 1, fun h hh => ?_, fun W _ _ y _ => ?_⟩
    · have h1 : h = 1 := Finset.mem_singleton.1 (Finsupp.support_single_subset hh)
      subst h1
      exact ⟨fun v _ => map_one _, map_one _⟩
    · simp
  | insert w S hw ih =>
    intro hK hC
    obtain ⟨T₁, hT₁s, hT₁⟩ := ih (fun v hv => hK v (Finset.mem_insert_of_mem hv))
      (fun v hv => hC v (Finset.mem_insert_of_mem hv))
    obtain ⟨T₂, hT₂s, hT₂⟩ := GlobalTheory.T.localCutOperator_transfer_adelicWhittaker E m w (ψ w) (hψ w) K (U w) (hK w (Finset.mem_insert_self _ _))
      (cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}
      (hC w (Finset.mem_insert_self _ _))
    refine ⟨comp T₁ T₂, fun k hk => ?_, fun W hN hKW y hy => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_comp hk
      obtain ⟨g, rfl⟩ := hT₂s b hb
      have hb' := (GlobalTheory.JSW.WhitModel.loc_mem_supS (insert w S) w g).2 (Or.inl (Finset.mem_insert_self _ _))
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [map_mul, (hT₁s a ha).1 v (fun h => hv (Finset.mem_insert_of_mem h)), hb' v hv, one_mul]
      · rw [map_mul, (hT₁s a ha).2, pInf_finGL, one_mul]
    · have hyh : ∀ h ∈ T₁.support, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (y * h) =
          GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y := fun h hh => by
        rw [map_mul, (hT₁s h hh).1 w hw, mul_one]
      have hyS := hT₁ W hN hKW y (fun v hv => hy v (Finset.mem_insert_of_mem hv))
      have hyw := hy w (Finset.mem_insert_self _ _)
      rw [act_comp]
      by_cases hyc : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈
          cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))
      · rw [act_congr T₁ (f' := W) fun k hk => ?_, hyS]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, true_and]
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_mem]
          rw [Set.mem_setOf_eq, hyh k hk]; exact hyc
      · rw [act_congr T₁ (f' := 0) fun k hk => ?_]
        · simp only [Set.indicator, Set.mem_setOf_eq, Finset.forall_mem_insert, hyc, false_and, if_false]
          unfold GlobalTheory.JSW.Cut.act; simp
        · rw [hT₂ W hN hKW (y * k) (by rw [hyh k hk]; exact hyw), Set.indicator_of_notMem]
          · rfl
          · rw [Set.mem_setOf_eq, hyh k hk]; exact hyc

end GlobalTheory.JSW.CutProd

theorem _root_.GlobalTheory.JSW.CutProd.cut_prod_mirS : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  intro E _ _ _ m S ψ hψ K U z hK hC
  obtain ⟨T, hTs, hT⟩ := GlobalTheory.JSW.CutProd.exists_cut_prod ψ hψ K U z S hK hC
  exact ⟨T, hTs, fun W hN hKW p hp => hT W hN hKW p fun w _ => GlobalTheory.JSW.CutProd.lr_loc_of_mem_mirS hp w⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositeCutOperatorsProductLocalCellsMirabolicStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : HeightOneSpectrum (𝓞 E), AddChar (w.adicCompletion E) ℂ), (∀ w x, ψ w x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (z : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) → (∀ w ∈ S, GlobalTheory.JSW.Cut.Cuts (ψ w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) (GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1}) → ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.Cut.act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ GlobalTheory.JSW.Cut.cell (z w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
  first | exact @GlobalTheory.JSW.CutProd.cut_prod_mirS | exact GlobalTheory.JSW.CutProd.cut_prod_mirS | (intros; apply GlobalTheory.JSW.CutProd.cut_prod_mirS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroupStatement

section

@[expose] public section

open Matrix Topology

theorem _root_.GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  first
  | exact @GlobalTheory.JSW.Cut.exists_cut_cor_of_sub
  | exact GlobalTheory.JSW.Cut.exists_cut_cor_of_sub
  | (intros; apply GlobalTheory.JSW.Cut.exists_cut_cor_of_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlaceStandardCharLocallyConstantNontrivialStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ ψ : AddChar (w.adicCompletion E) ℂ, (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) ∧ IsLocallyConstant ψ ∧ ψ ≠ 1 := by
  first | exact @GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | exact GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one | (intros; apply GlobalTheory.JSW.psiLoc_addChar_locallyConstant_ne_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerIndicatorCutMulOpenSubgroup

section

@[expose] public section

open Matrix Topology

namespace GlobalTheory.JSW.Cut

theorem cuts_mul_open_subgroup {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ}
    (U : Subgroup (GL (Fin n) F)) (hU : IsOpen (U : Set (GL (Fin n) F))) (X A : Set (GL (Fin n) F))
    (hX : ∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) (h : Cuts ψ (U : Set (GL (Fin n) F)) X A) :
    ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧
      Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  obtain ⟨T, hT⟩ := h
  let U₁ : Subgroup (GL (Fin n) F) :=
    { carrier := {u | u ∈ U ∧ ∀ k ∈ T.support, k⁻¹ * u * k ∈ U}
      one_mem' := ⟨one_mem _, fun k _ => by simpa using one_mem U⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun k hk => by
        have := mul_mem (ha.2 k hk) (hb.2 k hk)
        simpa [mul_assoc] using this⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun k hk => by
        have := inv_mem (ha.2 k hk)
        simpa [mul_assoc] using this⟩ }
  refine ⟨U₁, fun u hu => hu.1, ?_, T, ?_⟩
  · have : (U₁ : Set (GL (Fin n) F)) = (U : Set (GL (Fin n) F)) ∩
        ⋂ k ∈ T.support, (fun u : GL (Fin n) F => k⁻¹ * u * k) ⁻¹' (U : Set (GL (Fin n) F)) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      rfl
    rw [this]
    exact hU.inter (isOpen_biInter_finset fun k _ =>
      hU.preimage ((continuous_const.mul continuous_id).mul continuous_const))
  · rintro f hf hfU g ⟨a, ha, u, hu, rfl⟩
    have h1 : act T f (a * u) = act T f a := by
      unfold act
      refine Finset.sum_congr rfl fun k hk => ?_
      have e : a * u * k = a * k * (k⁻¹ * u * k) := by group
      simp only
      rw [e, hfU _ (hu.2 k hk)]
    rw [h1, hT f hf hfU a ha]
    by_cases hx : a ∈ X
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hX a hx u hu.1), hfU u hu.1]
    · have hx' : a * u ∉ X := fun h' => hx (by simpa using hX _ h' u⁻¹ (inv_mem hu.1))
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

end GlobalTheory.JSW.Cut
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerIndicatorCutMulOpenSubgroupStatement

section

@[expose] public section

open Matrix Topology

theorem _root_.GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ} (U : Subgroup (GL (Fin n) F)), IsOpen (U : Set (GL (Fin n) F)) → ∀ X A : Set (GL (Fin n) F), (∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) → GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X A → ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mul_open_subgroup | exact GlobalTheory.JSW.Cut.cuts_mul_open_subgroup | (intros; apply GlobalTheory.JSW.Cut.cuts_mul_open_subgroup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlaces

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

theorem cuts_mir {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ)
    (hψ : IsLocallyConstant ψ) (hψ1 : ψ ≠ 1) (m : ℕ) (U : Subgroup (GL (Fin (m + 1)) F))
    (hUc : IsCompact (U : Set (GL (Fin (m + 1)) F))) (hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)))
    (z : GL (Fin (m + 1)) F) : Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (cell z (U : Set (GL (Fin (m + 1)) F)))
      {p | lr p = lr 1} := by
  induction m with
  | zero =>
    classical
    have h1 : ∀ q : GL (Fin (0 + 1)) F, lr q = lr 1 → q = 1 := fun q hq => by
      obtain ⟨h, x, rfl⟩ := exists_mir hq
      rw [Subsingleton.elim h 1, Subsingleton.elim x 0, mir_one]
    refine ⟨Finsupp.single 1 (if (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F)) then 1 else 0),
      fun f _ _ g hg => ?_⟩
    rw [h1 g hg, act_single, mul_one]
    by_cases h : (1 : GL (Fin (0 + 1)) F) ∈ cell z (U : Set (GL (Fin (0 + 1)) F))
    · rw [if_pos h, one_mul, Set.indicator_of_mem h]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem h]
  | succ m ih =>
    refine GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs ψ hψ hψ1 m (GlobalTheory.T.exists_whittakerCut_inductionStep_of_open_subgroup ψ hψ hψ1 m (fun V hVc hVo z' => ?_)) U hUc hUo z
    refine GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup ψ V hVo _ _ (fun x hx u hu => ?_) (ih V hVc hVo z')
    obtain ⟨n, hn, k, hk, rfl⟩ := hx
    exact ⟨n, hn, k * u, V.mul_mem hk hu, by rw [mul_assoc]⟩

end GlobalTheory.JSW.Cut


open GlobalTheory.JSW.Cut in
theorem GlobalTheory.JSW.MirPatch.cut_operators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (n : ℕ) (h : Fin n → GA E (m + 1)) (c : Fin n → ℂ), (∀ i, h i ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), ∑ i, c i * W (p * h i) = (GlobalTheory.JSW.MirPatch.cell K q).indicator W p := by
  intro E _ _ _ m S K hKo hKc q
  classical
  obtain ⟨U, N, z, hU, hdisj, hchar⟩ := GlobalTheory.T.mirabolic_cell_finite_union_local_double_cosets E m S K hKo hKc q
  choose ψ hψv hψl hψ1 using GlobalTheory.T.finitePlace_standardChar_locallyConstant_nontrivial E
  have hcut : ∀ i : Fin N, ∃ T : GA E (m + 1) →₀ ℂ, (∀ h ∈ T.support, h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧
      GeneralLinearGroup.map (pInf E) h = 1) ∧ ∀ W : GA E (m + 1) → ℂ,
      (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
      (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m),
      act T W p = {x : GA E (m + 1) | ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈
        GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}.indicator W p := by
    intro i
    refine GlobalTheory.T.composite_cut_operators_product_local_cells_mirabolic E m S ψ hψv K U (z i) (fun w hw => (hU w hw).2.2) fun w hw => ?_
    haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion E w
    haveI : IsUltrametricDist (w.adicCompletion E) :=
      inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
        (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
    exact cuts_mir (ψ w) (hψl w) (hψ1 w) m (U w) (hU w hw).1 (hU w hw).2.1 (z i w)
  choose T hTs hT using hcut
  obtain ⟨n, h, c, hh, he⟩ := exists_fin (∑ i, T i)
  refine ⟨n, h, c, fun j => ?_, fun W hW hWK p hp => ?_⟩
  · obtain ⟨i, -, hi⟩ := Finsupp.mem_support_finsetSum _ (hh j)
    exact (hTs i _ hi).1
  · rw [← he, act_finset_sum]
    simp_rw [fun i => hT i W hW hWK p hp]
    by_cases hc : p ∈ GlobalTheory.JSW.MirPatch.cell K q
    · obtain ⟨i, hi⟩ := (hchar p hp).1 hc
      rw [Set.indicator_of_mem hc, Finset.sum_eq_single i]
      · exact Set.indicator_of_mem (s := {x : GA E (m + 1) | _}) hi _
      · intro j _ hj
        exact Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hj' => hj (hdisj p hp j i hj' hi)) _
      · simp
    · rw [Set.indicator_of_notMem hc]
      refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (s := {x : GA E (m + 1) | _}) (fun hi => hc ((hchar p hp).2 ⟨i, hi⟩)) _
end
end
end
