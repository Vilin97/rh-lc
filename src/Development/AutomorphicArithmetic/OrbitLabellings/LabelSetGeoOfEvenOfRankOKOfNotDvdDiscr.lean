module

public import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
public import Formalism.LocalToGlobal.CharacterGerms.SelfConjugateRowData
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralCStatement
public import Development.AutomorphicArithmetic.OrbitLabellings.BlkMemSSelfConjugatePlacesOfCMDatum
public import Development.AutomorphicArithmetic.OrbitLabellings.LabelSetEvOfGeoOfNotDvdDiscr
public import Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfLabelSetArith
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
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
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Formalism.LocalToGlobal.CharacterGerms.RankMaximalSelfUnconditional
public import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
public import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NuLocCLeNuPlEBaseChange
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAxesSelfSt
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm
public import Formalism.SharpRestriction.GrowthBounds.CoeffIdentitySelfConjHolds
public import Formalism.SharpRestriction.GrowthBounds.ExponentialPartialDerivatives
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieVals

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.ValBlocksSOfBlkMemS

section

@[expose] public section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.valBlocksS_of_blkMemS :
    ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) [NeZero d] (hd : ZMod d), hd + hd = 0 →
    ∀ (Orb : Type) [Fintype Orb] (I J : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ) (FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)) (ν : ℝ),
    ValO X n FFimg ν → ∀ (F : ∀ o, RF.Flag (X o)) (nW : ℕ), nW ≤ 2 * n + 1 → ∀ ga : Orb → ZMod d → ℕ → ℕ,
    PlaneBlockProductsMemFamily hd X n F FFimg ga → (∀ o, (X o).Alt) → (∀ o, (X o).j' < (X o).n) →
    (∀ o s, (X o).rkF 1 (s + hd) = (X o).rkF 0 s) → (∀ o s k, ga o s k ≠ 0 → k ≤ (X o).rkF 0 s) →
    ValBlocksS hd X F nW ga ν := by
  intro C _ _ V d _ hd hhd Orb _ I J _ _ X n FFimg ν hV F nW hnW ga hMem hAlt hj hrk hga
  intro L hAtt hOne hRows hWt
  have hwt : ∀ o, ∀ q ∈ L o, ∀ (g : Fin 2) (a : ZMod d) (k : ℕ),
      GlobalTheory.wt (X o) q.1 g a k ≠ 0 → k ≤ (X o).rkF g a := by
    intro o q hq g a k hne
    fin_cases g
    · have hle : GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k ≤ ga o a k := by
        rw [← hWt o a k]
        exact le_sum_map (L o) (fun q => GlobalTheory.wt (X o) q.1 0 a k + GlobalTheory.wt (X o) q.1 1 (a + hd) k) hq
      apply hga o a k
      have : GlobalTheory.wt (X o) q.1 0 a k ≠ 0 := hne
      omega
    · have hs : a + hd + hd = a := by rw [add_assoc, hhd, add_zero]
      have hle : GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k ≤ ga o (a + hd) k := by
        rw [← hWt o (a + hd) k]
        exact le_sum_map (L o)
          (fun q => GlobalTheory.wt (X o) q.1 0 (a + hd) k + GlobalTheory.wt (X o) q.1 1 (a + hd + hd) k) hq
      rw [hs] at hle
      have hne' : GlobalTheory.wt (X o) q.1 1 a k ≠ 0 := hne
      have h0 : ga o (a + hd) k ≠ 0 := by omega
      have := hga o (a + hd) k h0
      rw [← hrk o (a + hd), hs] at this
      exact this
  have hOK : ∀ o, ∀ q ∈ L o, GlobalTheory.AttainsOK (X o) (F o) q.1 q.2 := fun o q hq =>
    attainsOK_of (X o) (F o) (Or.inl (hAlt o)) (hj o) q.1 q.2 (hwt o q hq) (hAtt o q hq)
  have hsum : ∑ o, (List.map (fun q => GlobalTheory.what₂ (X o).n q.1) (L o)).sum ≤ n := by omega
  exact val_lists hV jetProd F L hOK hsum (hMem L hOne hWt)
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Flag

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {m : ZMod d → ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

def idxS (hd : ZMod d) (g : Fin 2) (t : ZMod d) : ZMod d := if g = 0 then t else t - hd

theorem rkF_sigmaS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd)
    (g : Fin 2) (t : ZMod d) : X.rkF g t = m (idxS hd g t) := by
  unfold RowData.rkF
  refine Finset.card_eq_of_equiv_fin
    ((Equiv.subtypeEquivRight fun c => ?_).trans (Equiv.sigmaSubtype (idxS hd g t)))
  rw [Finset.mem_filter, hty]
  simp only [Finset.mem_univ, true_and]
  unfold idxS
  by_cases hg : g = 0
  · simp only [if_pos hg]
  · simp only [if_neg hg]
    exact eq_sub_iff_add_eq.symm

def stdFlagS (hd : ZMod d) (X : RowData C V d (fun _ => Σ a : ZMod d, Fin (m a)) J)
    (hty : ∀ (g : Fin 2) (x : Σ a : ZMod d, Fin (m a)), (X.G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd) :
    Flag X where
  en := fun g t q => ⟨idxS hd g t, ⟨q.val, (rkF_sigmaS hd X hty g t) ▸ q.isLt⟩⟩
  en_inj := fun g t q q' h => by
    have h1 := eq_of_heq (Sigma.mk.inj h).2
    exact Fin.ext (Fin.mk.inj_iff.1 h1)
  en_ty := fun g t q => by
    rw [hty]
    unfold idxS
    by_cases hg : g = 0
    · simp [hg]
    · simp [hg]

end Flag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTieMain

section

@[expose] public section

set_option autoImplicit false

namespace Formalism.L2.FormalSeriesBounds

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem descent_holds : DescentSt Xo c :=
  GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw l Xo c

end Formalism.L2.FormalSeriesBounds
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds

end Formalism.L2.FormalSeriesBounds
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEig

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePPTDone

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
end
end

-- Source module: Development.AutomorphicArithmetic.OrbitLabellings.LabelSetGeoOfEvenOfRankOKOfNotDvdDiscr

section

@[expose] public section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

private def pairColsS (n : ℕ) : Fin (n / 2) × Fin 2 ↪ Fin n where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.2; have := x.2.2; omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : 2 * a.val + b.val = 2 * a'.val + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

theorem UpperTheory.labelSetGeo_of_even_of_rankOK_of_not_dvd_discr :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    y.IsAlg →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ¬ (V.l : ℤ) ∣ NumberField.discr E → Even d → lab.RankOK Dw → (∀ o s, lab.big o 0 s ↔ Even s.val) → lab.j' < lab.n →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (ga : Orb → ZMod d → ℕ → ℕ),
    (∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ Dw.mult (lab.tau o s)) → WtTieS Dw.mult lab.tau ga (fun τ i => a (τ, i)) →
    ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW →
    ∃ (X : ∀ o, RowData C V d (fun _ => lab.II Dw o) (JJ fun _ => lab.II Dw o)) (F : ∀ o, RF.Flag (X o)),
      (∀ o, (X o).n = lab.n ∧ (X o).m = lab.j + lab.j' ∧ (X o).Alt ∧ ∀ s, (X o).rkF 0 s = Dw.mult (lab.tau o s)) ∧
      ValBlocksS lab.hd X F nW ga ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY halg Orb _ d _ lab ha hdisc hev hr hbig hj
    a ga hsupp htie nW ν hν
  have hg : LabSGeo C3 ι Y lab := UpperTheory.labelSetGeo_of_labelSetArith E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hR2 : RankMaximalSelfCharts Xo c := rank_maximal_self_charts_of_nondegenerate Xo c rank_maximal_self_unconditional (GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c)
  have hCart : CartSelfSt := cartesian_self_conj_of_stability ptSelf_holds hStabSelf_holds
  have Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V := fun o =>
    { charZero := inferInstance
      algClosed := Y.algClosed
      l_odd := Y.l_odd
      k_unit := Y.k_unit
      cartH := hCart C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
      rank := rankHyp_ofLabS ha hg hr o
      axes := axesSelf_holds C V (𝓞 E) _ Y d _ (selfOfLab ha hg o)
      G0 := SelfConjugateGermZero.germ_zero_self_conjugate C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) _
      CEq := cEqSelf_holds C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
      R1 := independence_bound_self_conjugate C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (rankHyp_ofLabS ha hg hr o) _
        (hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
      R2 := hR2 hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hr o _
      CH := UpperTheory.labelSet_ev_of_geo_of_not_dvd_discr hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY halg Orb d lab ha hg hdisc hev hr hbig o _ }
  have hty : ∀ o (g : Fin 2) (x : lab.II Dw o),
      ((rdS Y (selfOfLab ha hg) Hy o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + lab.hd := fun _ _ _ => rfl
  have hrk : ∀ o g t, (rdS Y (selfOfLab ha hg) Hy o).rkF g t = Dw.mult (lab.tau o (idxS lab.hd g t)) :=
    fun o g t => rkF_sigmaS (m := fun s => Dw.mult (lab.tau o s)) lab.hd _ (hty o) g t
  have hrk0 : ∀ o s, (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s = Dw.mult (lab.tau o s) := fun o s => hrk o 0 s
  have hrk1 : ∀ o s, (rdS Y (selfOfLab ha hg) Hy o).rkF 1 (s + lab.hd) = (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s := by
    intro o s
    rw [hrk0, hrk]
    have e : idxS lab.hd 1 (s + lab.hd) = s := by
      unfold idxS
      rw [if_neg (by decide), add_sub_cancel_right]
    rw [e]
  have hA : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt := fun o => ⟨hev, hbig o⟩
  have hsupp' : ∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s := by
    intro o s k' h
    rw [hrk0]
    exact hsupp o s k' h
  refine ⟨fun o => rdS Y (selfOfLab ha hg) Hy o,
    fun o => stdFlagS (m := fun s => Dw.mult (lab.tau o s)) lab.hd _ (hty o),
    fun o => ⟨rfl, rfl, hA o, hrk0 o⟩, ?_⟩
  exact UpperTheory.valBlocksS_of_blkMemS C V d lab.hd ha.hd_two Orb _ _ _ (nW / 2) _ ν
    (RF.valO_self Y (selfOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW ν
      (hν.trans (descent_holds Xo c T io y C3 C V ι hι k Y hY a nW)) (selfSep_ofLab ha hg)
      (valuation_eq_self_of_unit_germ Y _ _ _ nW (unitSelf_holds Y _) (germLiftSelf_holds Y _ _)) (pairColsS nW))
    _ nW (by omega) ga
    (UpperTheory.blkMemS_selfConjugate_places_of_CMDatum E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg Hy a (nW / 2) nW (pairColsS nW) _ ga
      (fun _ _ _ _ => rfl) hA hj hsupp' htie)
    hA (fun _ => hj) hrk1 (fun o s k' h => (hsupp' o s k' h).2)
end
end
