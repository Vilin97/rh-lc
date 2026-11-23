module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransferAlt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
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
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbA
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Topology.Instances.Matrix
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import GroundTheory.AutomorphicForms.GLnLocal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FiberLocalization.EqZeroOfFiberEquivariant
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.DistrC
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Pieces
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.T2SpaceCentralizerGroup
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.ExistsConj
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsClosedRank
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OneFormsMapOfFunctorMorphismSmul
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransfer

section

@[expose] public section

noncomputable section

open PositivityTheory.PfBern.Frob PositivityTheory.RgUd.TP.Desc.Piece.Tr

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrDbl

theorem doubleTransfer : FrobeniusReciprocity → DoubleTransfer := by
  intro hF G _ _ _ _ _ _ _ _ _ H₁ H₂ _ _ hH₁ hH₂ hG hU₁ hU₂ X _ _ _ _ _ _ p₁ p₂ hc₁ hc₂ hp₁ hp₂ C hC hCinv hE₂ E hE
  obtain ⟨Fr₁, hs₁, -⟩ := hF G H₁ hH₁ hG hU₁ X p₁ hc₁ hp₁ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  obtain ⟨Fr₂, hs₂, -⟩ := hF G H₂ hH₂ hG hU₂ X p₂ hc₂ hp₂ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  set ξ := Fr₁.symm ⟨E, hE⟩
  have h2 : SupportedIn (↑ξ) C := (hs₂ ξ C hC hCinv).2 (hE₂ _ (Fr₂ ξ).2)
  have h1 := (hs₁ ξ C hC hCinv).1 h2
  simpa [ξ] using h1

end PositivityTheory.RgUd.TP.Desc.Piece.TrDbl
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbB

section

@[expose] public section

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}

theorem rank_eq_of_idem {R : Type*} [Field R] {P Q : Matrix (Fin N) (Fin N) R} (hP : P * P = P) (hQ : Q * Q = Q)
    (hu : IsUnit (Q * P + (1 - Q) * (1 - P)).det) : P.rank = Q.rank := by
  set u := Q * P + (1 - Q) * (1 - P)
  have h1 : u * P = Q * P := by
    simp only [u, add_mul, mul_assoc, sub_mul, one_mul, hP, sub_self, mul_zero, add_zero]
  have h2 : Q * u = Q * P := by
    simp only [u, mul_add, ← mul_assoc, mul_sub, mul_one, hQ, sub_self, zero_mul, add_zero]
  have : (u * P).rank = (Q * u).rank := by rw [h1, h2]
  rwa [rank_mul_eq_right_of_isUnit_det u P hu, rank_mul_eq_left_of_isUnit_det u Q hu] at this

theorem isClosed_idem_rank (n : ℕ) : IsClosed {P : Matrix (Fin N) (Fin N) k | P * P = P ∧ P.rank = n} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro Q hQ
  by_cases hi : Q * Q = Q
  · have hr : Q.rank ≠ n := fun h => hQ ⟨hi, h⟩
    refine ⟨{P | (Q * P + (1 - Q) * (1 - P)).det ≠ 0}, fun P hP hP' => hr ?_, ?_, ?_⟩
    · rw [← hP'.2]
      exact (rank_eq_of_idem hP'.1 hi (isUnit_iff_ne_zero.2 hP)).symm
    · exact isOpen_ne_fun (((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_const.sub continuous_id))).matrix_det) continuous_const
    · show (Q * Q + (1 - Q) * (1 - Q)).det ≠ 0
      have : Q * Q + (1 - Q) * (1 - Q) = 1 := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hi]; abel
      rw [this, det_one]; exact one_ne_zero
  · exact ⟨{P | P * P ≠ P}, fun P hP hP' => hP hP'.1, isOpen_ne_fun (continuous_id.mul continuous_id) continuous_id,
      hi⟩

theorem orbClosed_gen (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (hA : IsReduced A)
    (b : Fin r → A) (hb : Submodule.span k (Set.range b) = ⊤) (ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k) :
    IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val} := by
  classical
  let L : (Fin r → k) → A := fun c => ∑ i, c i • b i
  let Φ : (Fin r → Matrix (Fin N) (Fin N) k) → (Fin r → k) → Matrix (Fin N) (Fin N) k :=
    fun w c => ∑ i, c i • w i
  have hL : ∀ a, ∃ c, L c = a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun k).1 (hb ▸ Submodule.mem_top)
  choose s hs using hL
  have Lsub : ∀ c c', L (c - c') = L c - L c' := fun c c' => by
    simp only [L, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φsub : ∀ w c c', Φ w (c - c') = Φ w c - Φ w c' := fun w c c' => by
    simp only [Φ, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φadd : ∀ w c c', Φ w (c + c') = Φ w c + Φ w c' := fun w c c' => by
    simp only [Φ, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have Φsmul : ∀ w (t : k) c, Φ w (t • c) = t • Φ w c := fun w t c => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have Lsingle : ∀ i, L (Pi.single i 1) = b i := fun i => by
    simp [L, Pi.single_apply]
  have Φsingle : ∀ w i, Φ w (Pi.single i 1) = w i := fun w i => by
    simp [Φ, Pi.single_apply]
  have hΦc : ∀ c : Fin r → k, Continuous fun w : Fin r → Matrix (Fin N) (Fin N) k => Φ w c := fun c =>
    continuous_finsetSum _ fun i _ => (continuous_apply i).const_smul (c i)
  let S : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
    (⋂ c, ⋂ (_ : L c = 0), {w | Φ w c = 0}) ∩ ((⋂ a, ⋂ a', {w | Φ w (s (a * a')) = Φ w (s a) * Φ w (s a')}) ∩
      ({w | Φ w (s 1) = 1} ∩ ⋂ e, ⋂ (_ : IsIdempotentElem e),
        (fun w => Φ w (s e)) ⁻¹' {P | P * P = P ∧ P.rank = (ρ₀ e).rank}))
  have hS : IsClosed S := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_eq (hΦc c) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun a' =>
        isClosed_eq (hΦc _) ((hΦc _).mul (hΦc _))
    · exact isClosed_eq (hΦc _) continuous_const
    · exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        (isClosed_idem_rank (ρ₀ e).rank).preimage (hΦc (s e))
  convert hS using 1
  ext w
  simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨g, hg⟩
    have hΦ : ∀ c, Φ w c = g.val * ρ₀ (L c) * g⁻¹.val := fun c => by

      simp only [Φ, L, hg, map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    have hgi : g⁻¹.val * g.val = 1 := Units.inv_mul g
    refine ⟨fun c hc => by rw [hΦ, hc, map_zero, mul_zero, zero_mul], fun a a' => ?_, ?_, fun e he => ?_⟩
    · rw [hΦ, hΦ, hΦ, hs, hs, hs, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul]
    · rw [hΦ, hs, map_one, mul_one, Units.mul_inv]
    · rw [hΦ, hs]
      refine ⟨?_, ?_⟩
      · have := congrArg ρ₀ he.eq
        rw [map_mul] at this
        simp only [mul_assoc]
        rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul, ← mul_assoc (ρ₀ e), this]
      · rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units g⁻¹),
          rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units g)]
  · rintro ⟨h0, hmul, h1, hrk⟩
    have hwd : ∀ c c', L c = L c' → Φ w c = Φ w c' := fun c c' h => by
      have := h0 (c - c') (by rw [Lsub, h, sub_self])
      rwa [Φsub, sub_eq_zero] at this
    let ρl : A →ₗ[k] Matrix (Fin N) (Fin N) k :=
      { toFun := fun a => Φ w (s a)
        map_add' := fun a a' => by
          rw [← Φadd]; apply hwd; rw [hs]
          simp only [L, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, show (∑ i, s a' i • b i) = L (s a') from rfl, hs, hs]
        map_smul' := fun t a => by
          rw [RingHom.id_apply, ← Φsmul]; apply hwd; rw [hs]
          simp only [L, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, hs] }
    let ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k := AlgHom.ofLinearMap ρl h1 hmul
    have hρ : ∀ a, ρ a = Φ w (s a) := fun _ => rfl
    obtain ⟨g, hg⟩ := orbHom_gen k N A hA ρ₀ ρ fun e he => by rw [hρ, (hrk e he).2]
    refine ⟨g, fun i => ?_⟩
    rw [← hg, hρ, ← Φsingle w i]
    apply hwd
    rw [hs, Lsingle]

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OrbClosed

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbHom : Tr.OrbHom k := fun N A _ _ _ hA ρ ρ' h => orbHom_gen k N A hA ρ ρ' h

theorem orbClosed : Tr.OrbClosed k := fun N r A _ _ _ hA b hb ρ₀ => orbClosed_gen N r A hA b hb ρ₀

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TransferOf

section

@[expose] public section

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker MeasureTheory

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop
open PositivityTheory.PfBern.Loc (SC restr restr_surjective pullL mulInd)
open PositivityTheory.PfBern.Frob (FrobeniusReciprocity IsUnimod eqvF translF Fib fibSmul)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def actH {N : ℕ} (g : GL (Fin N) k) : Sp k N ≃ₜ Sp k N where
  toFun := act g
  invFun := act g⁻¹
  left_inv q := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv q := by rw [← act_mul, mul_inv_cancel, act_one]
  continuous_toFun := Continuous.actc continuous_const continuous_id
  continuous_invFun := Continuous.actc continuous_const continuous_id


theorem transfer_of : (PositivityTheory.PfBern.Frob.FrobeniusReciprocity → DoubleTransfer) → OrbHom k → OrbClosed k → Transfer k := by
  intro hDT hOH hOC hFr p _ _ hU N q Z hZ χ D τ x₀ hx₀ hV ξ hsupp hinv f hf
  haveI : T2Space k := t2k
  haveI : TotallyDisconnectedSpace k := tdk
  haveI : SecondCountableTopology k := sck
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := tdM
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) k) := inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → k))
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  letI : MeasurableSpace (GL (Fin N) k) := borel _
  haveI : BorelSpace (GL (Fin N) k) := ⟨rfl⟩
  have hP := pieceTop k N q Z hZ χ D τ
  have hCR : CR (Sx D x₀) := hP.2.2 x₀ hx₀
  have hB0 : x₀ ∈ Bz Z := hx₀.1
  have hχ0 : aeval x₀ χ = 0 := hx₀.2.1
  obtain ⟨e₁, he₁⟩ := exists_orb_homeo hOC hZ D.hz
  obtain ⟨e₂, he₂⟩ := exists_orb_homeo hOC hCR (sx_span D hB0 hχ0)
  have hYc : IsClosed (Ys D τ) := isClosed_Ys D hOC hZ τ hP.2.1
  haveI : LocallyCompactSpace (Ys D τ) := hYc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hp₁ := oneFormsMapOfFunctorMorphism_smul (τ := τ) he₁
  have hp₂ := second_orbit_map_equivariant (τ := τ) (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂
  let C : Set (Ys D τ) := {y | y.1.2.2 = 0}
  have hCc : IsClosed C := isClosed_eq (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
  have hCinv : ∀ (g : GL (Fin N) k), ∀ y ∈ C, g • y ∈ C := by
    intro g y hy
    change g.val *ᵥ y.1.2.2 = 0
    rw [show y.1.2.2 = 0 from hy, Matrix.mulVec_zero]

  have hyp : ∀ E ∈ eqvF hp₂ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS (Sx D x₀)).subtype),
      PositivityTheory.PfBern.Frob.SupportedIn E (Subtype.val ⁻¹' C) := by
    intro E hEeqv φ0 hφ0
    let hY := hY2 (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂
    have hY2c : IsClosed (Ys2 D τ x₀) := isClosed_second_fibre_set hOC hZ x₀
    let E' : PositivityTheory.PfBern.Loc.Distr (Ys2 D τ x₀) := E.comp (pullL hY)
    obtain ⟨η, hη⟩ := exists_functional hY2c E'
    have hSη : Supp η (Bz (Sx D x₀) ×ˢ Set.univ) := by
      intro f hf1 hvan
      have hr : restr hY2c ⟨f, hf1.1⟩ = 0 := Subtype.ext (funext fun y => hvan y.1 (Ys2_sub hB0 hχ0 y.2))
      have := hη ⟨f, hf1.1⟩
      rw [hr, map_zero] at this
      exact this
    have hIη : Inv (Sx D x₀) η := by
      intro h hh f hf1
      let hH : GzS (Sx D x₀) := ⟨h, hh⟩
      let f1 : SC (Sp k N) := pullL (actH k h) ⟨f, hf1.1⟩
      have key : pullL hY (restr hY2c f1) = translF hp₂ hH⁻¹ (pullL hY (restr hY2c ⟨f, hf1.1⟩)) := by
        apply Subtype.ext
        funext z
        change f (act h (hY z).1) = f (hY (fibSmul hp₂ hH⁻¹⁻¹ z)).1
        rw [second_fibre_homeomorph_smul he₂, inv_inv]
      have h1 : η (fun q => f (act h q)) = η f1 := rfl
      rw [h1, hη f1, hη ⟨f, hf1.1⟩]
      change E (pullL hY (restr hY2c f1)) = E (pullL hY (restr hY2c ⟨f, hf1.1⟩))
      rw [key]
      exact (hEeqv hH⁻¹ _).trans (by simp)
    have hkill := hV η hSη hIη
    let φ' : SC (Ys2 D τ x₀) := pullL hY.symm φ0
    obtain ⟨f0, hf0⟩ := restr_surjective hY2c φ'
    have hsupp' : Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {y | y.1.2 ≠ 0} := fun y hy => hφ0 hy
    have hK : IsCompact (Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ)) :=
      (isCompact_support φ'.2).image continuous_subtype_val
    have hKsub : Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {q : Sp k N | q.2 ≠ 0} := by
      rintro _ ⟨y, hy, rfl⟩
      exact hsupp' hy
    have hUo : IsOpen {q : Sp k N | q.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    obtain ⟨Bc, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between hK hUo hKsub
    let f : SC (Sp k N) := mulInd Bc ⟨hBc.isClosed, hBo⟩ f0
    have hrf : restr hY2c f = φ' := by
      apply Subtype.ext
      funext y
      change Bc.indicator 1 y.1 * (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y
      have e0 : (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y := congrFun (congrArg Subtype.val hf0) y
      by_cases hyB : y.1 ∈ Bc
      · simp [hyB, e0]
      · have : (φ' : Ys2 D τ x₀ → ℂ) y = 0 := by
          by_contra hne
          exact hyB (hKB ⟨y, hne, rfl⟩)
        simp [hyB, this]
    have hfU : (f : Sp k N → ℂ) ∈ supportedIn {q : Sp k N | q.2 ≠ 0} := by
      refine ⟨f.2, fun q hq => hBU ?_⟩
      by_contra hqB
      exact hq (by simp [f, mulInd, hqB])
    have hz := hkill f hfU
    rw [hη f, hrf] at hz
    have e2 : pullL hY φ' = φ0 := PositivityTheory.PfBern.Loc.pullL_pullL_symm hY φ0
    change E (pullL hY φ') = 0 at hz
    rw [e2] at hz
    exact hz

  have hPc : IsClosed (piece D τ ×ˢ (Set.univ : Set (Fin N → k))) := hP.1.prod isClosed_univ
  obtain ⟨Dd, hDd⟩ := exists_distr_on ξ hPc hsupp
  let hY1' := hY1 (τ := τ) e₁ he₁ hZ
  let E₁ : PositivityTheory.PfBern.Frob.Distr (Fib (p1 D τ e₁)) := Dd.comp (pullL hY1'.symm)
  have hE₁ : E₁ ∈ eqvF hp₁ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS Z).subtype) := by
    intro h φ
    obtain ⟨f0, hf0⟩ := restr_surjective hPc (pullL hY1'.symm φ)
    have hφ : ∀ w, (φ : Fib (p1 D τ e₁) → ℂ) w = (f0 : Sp k N → ℂ) (hY1' w).1 := fun w => by
      have := congrFun (congrArg Subtype.val hf0) (hY1' w)
      change (f0 : Sp k N → ℂ) (hY1' w).1 = (φ : Fib (p1 D τ e₁) → ℂ) (hY1'.symm (hY1' w)) at this
      rw [Homeomorph.symm_apply_apply] at this
      exact this.symm
    let f1 : SC (Sp k N) := pullL (actH k (h⁻¹).1) f0
    have e1 : pullL hY1'.symm (translF hp₁ h φ) = restr hPc f1 := by
      apply Subtype.ext
      funext y
      change (φ : Fib (p1 D τ e₁) → ℂ) (fibSmul hp₁ h⁻¹ (hY1'.symm y)) = (f0 : Sp k N → ℂ) (act (h⁻¹).1 y.1)
      rw [hφ, first_fibre_homeomorph_smul he₁ hZ, Homeomorph.apply_symm_apply]
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one, one_mul]
    change Dd (pullL hY1'.symm (translF hp₁ h φ)) = Dd (pullL hY1'.symm φ)
    rw [e1, ← hf0, ← hDd f1, ← hDd f0]
    exact hinv (h⁻¹).1 (h⁻¹).2 f0 ⟨f0.2, Set.subset_univ _⟩
  have hSupp := hDT hFr (GL (Fin N) k) (GzS Z) (GzS (Sx D x₀)) (isClosed_GzS Z) (isClosed_GzS _) (isUnimod_GL hU)
    (hU N Z hZ) (hU N _ hCR) (Ys D τ) (p1 D τ e₁) (p2 D τ hOH hZ hx₀ e₂) (continuous_first_orbit_map he₁) continuous_p2 hp₁ hp₂
    C hCc hCinv hyp E₁ hE₁
  have hz := hSupp (pullL hY1' (restr hPc ⟨f, hf.1⟩)) fun w hw hwC => hw (by
    change f w.1.1.2 = 0
    by_contra hne
    exact hf.2 hne hwC)
  rw [show ξ f = Dd (restr hPc ⟨f, hf.1⟩) from hDd ⟨f, hf.1⟩,
    ← PositivityTheory.PfBern.Loc.pullL_pullL_symm hY1'.symm (restr hPc ⟨f, hf.1⟩)]
  exact hz

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Transfer

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PTr

open PositivityTheory.RgUd.TP.Desc.Piece

theorem transfer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Transfer k :=
  TrI.transfer_of k TrDbl.doubleTransfer (TrOrb.orbHom k) (TrOrb.orbClosed k)

end PositivityTheory.RgUd.TP.Desc.Piece.PTr
end
end
