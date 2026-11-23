module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportInClassGeneral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExhAll
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLJCommC
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Mathlib.Tactic.Linter.Style
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOpOfPair

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLZero

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_zero_holds : SAZero := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he X hX y hy h0
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hw : 0 < Real.sqrt (MA.wq S.G.k y (D.parOf S v).TT) := by
    apply Real.sqrt_pos.2
    unfold MA.wq
    exact mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hy.1 l)) _)
      (pow_pos (sub_pos.2 hy.2) _)
  have hin : ∀ π, inner ℂ (B.hsVec (e π y.2)) (B.hsVec (X (B.gq (T v).base y))) = 0 := by
    intro π
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he X hX π
    have h := h0 π
    unfold trJ at h
    rw [En.toSm_val_of_mem _ hsm] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (Complex.ofReal_ne_zero.2 hw.ne')
    · exact h
  have hfib := En.fibre_membership_holds E Wp Wq S T v hplace X hX y hy
  rw [(he.2 y.2 hy.2).2.2 _ hfib]
  simp [hin]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLAsm

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem sAPairOne_of_parts (hZ : SAZero) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) :
    SAPairOne := by
  obtain ⟨C1, hZ'⟩ := hZ
  obtain ⟨C2, hL'⟩ := hL
  obtain ⟨C3, hE'⟩ := hE
  obtain ⟨C4, hJC'⟩ := hJC
  obtain ⟨C5, hB3'⟩ := hB3
  refine ⟨max C1 (max C2 (max C3 (max C4 C5))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θ hΘ K hK J hJ hΘK hΘJ hKt
  have mono : ∀ c : ℝ, c ≤ max C1 (max C2 (max C3 (max C4 C5))) → BuiltOW c S T f χ ν' m₀ top A₀ :=
    fun c h => ⟨isBuiltPlace_mono h hB.1, hB.2⟩
  have hB1 := mono C1 (le_max_left _ _)
  have hB2 := mono C2 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hB3 := mono C3 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hB4 := mono C4 (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hB5 := mono C5 (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs

  set Cs : Set (MA.E (D.parOf S v).r) :=
    ⋃ π, tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
      MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) with hCsdef
  have hCc : IsCompact Cs := isCompact_iUnion fun π => (hKt π).1
  have hCQ : Cs ⊆ Qs := Set.iUnion_subset fun π => (hKt π).2
  have hCcl : IsClosed Cs := hCc.isClosed
  have hK0 : ∀ y ∈ Qs, y ∉ Cs → K (B.gq (T v).base y) = 0 := by
    intro y hy hyC
    refine hZ' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he K hK y hy fun π => ?_
    have hn : y ∉ tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) := fun h => hyC (Set.mem_iUnion.2 ⟨π, h⟩)
    have h0 := image_eq_zero_of_notMem_tsupport hn
    simp only [MA.ext] at h0
    first
    | exact h0 hy
    | exact (dif_pos hy).symm.trans h0
  have hΘK0 : ∀ y ∈ Qs, y ∉ Cs → B.opApply Θ K (B.gq (T v).base y) = 0 := fun y hy hyC =>
    hL' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v Θ hΘ K hK (Qs \ Cs) ((MA.Qset_open _ _).sdiff hCcl)
      Set.sdiff_subset (fun y' hy' => hK0 y' hy'.1 hy'.2) y ⟨hy, hyC⟩
  refine ⟨fun π => ?_, ?_⟩
  ·
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he (B.opApply Θ K) hΘK π
    have hsupp : Function.support (MA.ext ((trJ S T v e (B.opApply Θ K) π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) ⊆ Cs := by
      intro y hy
      by_contra hyC
      apply hy
      by_cases hyQ : y ∈ Qs
      · simp only [MA.ext]
        unfold trJ
        rw [En.toSm_val_of_mem _ hsm]
        simp [hΘK0 y hyQ hyC, GA.hsVec_zero']
      · simp only [MA.ext]
        first
        | exact fun h => absurd h hyQ
        | exact dif_neg hyQ
    have hts := closure_minimal hsupp hCcl
    exact ⟨hCc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hCQ⟩
  ·
    obtain ⟨F₁, U₁, -, hCU₁, hF₁s, hF₁c, hF₁O, hF₁e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v K hK Cs hCc hCQ
    obtain ⟨F₂, U₂, hU₂o, hCU₂, hF₂s, hF₂c, hF₂O, hF₂e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v J hJ Cs hCc hCQ
    have hKF₁ : ∀ y ∈ Qs, K (B.gq (T v).base y) = B.JF (T v).base F₁ (B.gq (T v).base y) := by
      intro y hy
      by_cases hyU : y ∈ U₁
      · exact ((hF₁e y hy).1 hyU).symm
      · have hyC : y ∉ Cs := fun h => hyU (hCU₁ h)
        rw [hK0 y hy hyC, (hF₁e y hy).2 (hK0 y hy hyC)]
    have hc1 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₁ hF₁s hF₁c hF₁O Set.univ K isOpen_univ hK
      (fun y hy _ => hKF₁ y hy)
    have hc2 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₂ hF₂s hF₂c hF₂O U₂ J hU₂o hJ
      (fun y hy hyU => ((hF₂e y hy).1 hyU).symm)
    obtain ⟨hF₁5, hF₂5, hΘF₁5, hΘF₂5, hβ⟩ :=
      hB3' E Wp Wq S T f χ ν' m₀ top A₀ hB5 v Θ hΘ F₁ F₂ hF₁s hF₁c hF₁O hF₂s hF₂c hF₂O
    have hLp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he (B.opApply Θ K) J (B.opApply Θ F₁) F₂
      hΘK hJ hΘF₁5 hF₂5 (Filter.Eventually.of_forall fun y hy => ⟨(hc1 y hy trivial).1, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hΘK0 y hy hyC)
        exact ((hF₂e y hy).1 (hCU₂ hyC)).symm⟩)
    have hRp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he K (B.opAdj Θ J) F₁ (B.opAdj Θ F₂)
      hK hΘJ hF₁5 hΘF₂5 (Filter.Eventually.of_forall fun y hy => ⟨hKF₁ y hy, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hK0 y hy hyC)
        exact (hc2 y hy (hCU₂ hyC)).2⟩)
    rw [hLp, hRp]
    exact hβ

theorem sAPairL_of_parts (hF : JAFFStable) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) : SAPairL :=
  sAPairL_of_one hF (sAPairOne_of_parts self_adjoint_zero_holds hL hE hJC hB3)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLLocal

section

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def qOf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : (Fin r → ℂ) × ℂ :=
  (fun a => Formalism.QuantumDeterminants.cmin k r z z' g a, Formalism.QuantumDeterminants.zeta k r z z' g)

theorem qOf_contOn (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContinuousOn (qOf k r z z') (Q.OmPlus k r z z') := by
  refine ContinuousOn.prodMk ?_ ?_
  · refine continuousOn_pi.2 fun a => ?_
    unfold Formalism.QuantumDeterminants.cmin
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      (fun g hg => hg.1 _ (Nat.le_of_lt a.isLt))
  · unfold Formalism.QuantumDeterminants.zeta
    exact (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn.div (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.dmin_cont z z' _).continuousOn
      (fun g hg => hg.1 _ le_rfl)

theorem qOf_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : qOf k r D.z D.z' (B.sgs p g) = qOf k r D.z D.z' g := by
  unfold qOf Formalism.QuantumDeterminants.cmin Formalism.QuantumDeterminants.zeta
  simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]

theorem qOf_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') : qOf k r D.z D.z' (B.gq D q) = q :=
  Prod.ext (funext fun a => Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq D hq a) (Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq D hq)

theorem self_adjoint_locality_holds : SALocal := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ _hΘ K hK V hV hVQ hK0 y hy
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  let O : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    qOf S.G.k S.G.r (T v).base.z (T v).base.z' ⁻¹' V
  have hOo : IsOpen O :=
    (qOf_contOn _ _ _ _).isOpen_inter_preimage (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _) hV
  have hD : ∀ x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z', x ∈ Q.Glev S.G.k S.G.r 0 ∩
      {g | 0 < Gf S.G.k S.G.r (T v).base.z (T v).base.z' g ∧
        ∀ a : Fin S.G.r, Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    fun x hx => ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hx.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hx⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset S.G.k S.G.r, n ∈ Q.Nlev S.G.k S.G.r 0 :=
    fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have hKz : ∀ x ∈ B.GV S.G.k S.G.r, x ∈ O → K x = 0 := by
    intro x hxG hxO
    have hxOm : x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hxG, hxO.1⟩
    obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true _ _ _ _ (T v).base _ hxOm
    have hqV : q ∈ V := by
      have h1 : qOf S.G.k S.G.r (T v).base.z (T v).base.z' (B.sgs p (B.gq (T v).base q)) ∈ V := hxO.2
      rwa [qOf_sgs (T v).base hp, qOf_gq (T v).base hq] at h1
    have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have := LT.agree_sgs (T v).base K (fun _ => 0)
      (fun y hy n hn => hK.2.1 y (hD y hy) n (hNl n hn))
      (fun y hy n hn => hK.2.2.1 y (hD y hy) n (hNl n hn))
      (fun y hy h hh h' hh' => hK.2.2.2 y (hD y hy) h hh h' hh')
      (fun _ _ _ _ => (smul_zero _).symm) (fun _ _ _ _ => (smul_zero _).symm)
      (fun _ _ _ _ _ _ => by simp)
      hp hgq (hK0 q hqV)
    exact this
  have hyQ : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    ⟨(hVQ hy).1, by rw [← hTT]; exact (hVQ hy).2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hyQ
  have hg0O : B.gq (T v).base y ∈ O := by
    refine ⟨hg0.2, ?_⟩
    show qOf S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ V
    rw [qOf_gq (T v).base hyQ]; exact hy
  unfold B.opApply
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨Tm, _, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hOo Tm.word_lie hKz _ hg0.1 hg0O, map_zero]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_pairing_list_holds : SA.SAPairL :=
  SA.sAPairL_of_parts smooth_forms_stability_holds SA.self_adjoint_locality_holds (SA.sAExh_of_smooth SA.averaging_smoothness_holds) SA.self_adjoint_commutation_compact
    SA.compact_support_lemma_three

theorem star_operator_transfer_holds : JAStarOp := jAStarOp_of_pairL self_adjoint_pairing_list_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end
