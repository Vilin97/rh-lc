module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPEOm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliUnderIntegral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExh
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLQOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfExhaustOfAvgCutoff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLExhAll
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Tactic.Linter.Style
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComposeDifferentialOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsAgree
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLSAExh

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem average_one_cutoff_on_orbits : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff := avgCutoff_of_smooth averaging_smoothness_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPExh

section

@[expose] public section

open MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_exhaustion : RDSPExh := by
  intro k r Wp Wq _ _ _ _ _ _ D X hX C hC hCO
  have hX' : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
    rwa [rdb_ffl_om_eq] at hX
  have hqC : IsCompact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C) :=
    hC.image_of_continuousOn ((Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_contOn D.z D.z').mono fun g hg => (hCO hg).2)
  have hqQ : Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C ⊆ JF.QDom k r D.z D.z' := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D (hCO hg)).choose_spec.2.1
  obtain ⟨K', hK'c, hCK', hK'Q⟩ := exists_compact_between hqC (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hqQ
  obtain ⟨φ, hφ, ⟨C', hC'c, hC'O, hC'φ⟩, hint⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.average_one_cutoff_on_orbits k r Wp Wq D K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C' := by
    refine closure_minimal (fun g hg => ?_) hC'c.isClosed
    by_contra hgC
    exact hg (by simp [hC'φ g hgC])
  refine ⟨fun g => φ g • X g,
    Q.OmPlus k r D.z D.z' ∩ Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' ⁻¹' interior K', ?_, ?_, ?_,
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.isOpen_qOf D.z D.z' isOpen_interior, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨C'ᶜ, fun _ => 0, hC'c.isClosed.isOpen_compl, fun h => hO (hC'O h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hC'φ g hg]
  · exact hC'c.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · exact hsuppC.trans hC'O
  · intro g hg
    exact ⟨(hCO hg).2, hCK' ⟨g, hg, rfl⟩⟩
  · intro p hp g hg hs
    refine ⟨hg.2, ?_⟩
    have h2 := hs.2
    simp only [Set.mem_preimage] at h2 ⊢
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_sgs D hp] at h2
  · intro g hg
    have hJ : B.JF D (fun g => φ g • X g) g = (∫ p, φ (B.sgs p g) ∂D.μSS) • X g := by
      change ∫ p, JF.xiP D p • B.rho D p (fun g => φ g • X g) g ∂D.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hr : B.rho D p (fun g => φ g • X g) g = φ (B.sgs p g) • B.rho D p X g := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, Formalism.FourierDecayAlt.P.CutMP.JA.SA.eqv_of_FFl D X hX' hp hg]
    refine ⟨fun hgU => ?_, fun h0 => by rw [hJ, h0, smul_zero]⟩
    obtain ⟨p₀, hp₀, -, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
    have h1 := hint p₀ hp₀ _ (interior_subset hgU.2)
    rw [← hge] at h1
    rw [hJ, h1, one_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPIpSwap

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_pairing_inner_swap : RDSPIpSwap := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' μ Φ Ψ c
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _))
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) with he
  have happ : ∀ (c' : Cf r 0) (l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}), e c' l.1 = c' l := by
    intro c' l
    rw [he]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r => ℂ)
      (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) c' l
  have hglue : ∀ c' : Cf r 0, glue 0 c c' = e c' := fun c' => funext fun l => by
    simp only [glue]
    rw [dite_eq_left (show ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) from Nat.zero_le _)]
    exact (happ c' ⟨l, Nat.zero_le _⟩).symm
  have hprod : ∀ c' : Cf r 0,
      (∏ l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}, ‖c' l‖ ^ (-2 : ℤ)) = ∏ l : Fin r, (‖e c' l‖ ^ 2)⁻¹ := by
    intro c'
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)) _ _ (fun l => ?_)
    show ‖c' l‖ ^ (-2 : ℤ) = (‖e c' l.1‖ ^ 2)⁻¹
    rw [happ c' l, zpow_neg]
    norm_cast
  unfold radIp LocFacts₂ pairAt dxc
  simp only [B.hsInner]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← hmp.integral_comp']
  refine integral_congr_ae (ae_of_all _ fun c' => ?_)
  simp only
  rw [hglue c', ENNReal.toReal_ofReal (Finset.prod_nonneg fun _ _ => by positivity), Complex.real_smul, hprod c']

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPJFMem

section

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_orbital_membership : RDSPJFMem := by
  intro k r Wp Wq _ _ _ _ _ _ D F hF hcs hts
  have hpos : ∀ g ∈ tsupport F, (0 : ℝ) < Gf k r D.z D.z' g := fun g hg => (hts hg).2.2
  obtain ⟨ε, hε, hεle⟩ := hcs.isCompact.exists_forall_le' (PositiveOrbitOpen.gf_cont D.z D.z').continuousOn hpos
  have hnice : NiceAll D F := by
    refine ⟨ε, hε, hF, fun A m => compact_support_finite_class k r _ F (tsupport F) hF hcs.isCompact ?_ A m, ?_⟩
    · intro g hg
      by_contra h
      exact hg (subset_tsupport _ h)
    · intro g _ hg
      exact hεle g (subset_tsupport _ hg)
  refine ⟨(radial_orbital_niceness k r Wp Wq D F hnice).1, ?_⟩
  intro g _ hne
  by_contra hno
  push_neg at hno
  apply hne
  show ∫ p, _ ∂D.μSS = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [B5.ae_inSS D] with p hp
  have h0 : F (B.sgs p g) = 0 := by
    by_contra h
    exact hno p hp (subset_tsupport _ h)
  show _ • _ = (0 : Wq →L[ℂ] Wp)
  simp only [B.sgs] at h0
  rw [h0]
  simp

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPLoc

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_locality : RDSPLoc := by
  intro k r Wp Wq _ _ _ _ _ _ Θ U X Y hU hXY g hgU hgV
  have h : ∀ x ∈ B.GV k r, x ∈ U → X x = Y x := fun x hx hxU => hXY x hxU hx
  exact ⟨Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_congr Θ hU h hgV hgU,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hU h g hgV hgU⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPZeroR

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_zero_right : RDSPZeroR := by
  intro k r Wp Wq _ _ _ _ _ _ D X Y hX hY hxy g hg
  obtain ⟨p, hp, hq, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
  set q := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' g with hqdef
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨x, hxD, w, hw, hres⟩ := radial_group_residue k r Wp Wq D q hq
  have hxe : X (B.gq D q) = Y (B.gq D q) := by
    have e := rdsp_resG_congr X Y x (hxy x hxD)
    rw [hres X hX, hres Y hY] at e
    exact smul_right_injective _ hw e
  have hD : ∀ y ∈ JF.Om k r D.z D.z', y ∈ Q.Glev k r 0 ∩ JF.Om k r D.z D.z' := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  rw [hge]
  exact Formalism.FourierDecayAlt.P.CutMP.JA.LT.agree_sgs D X Y
    (fun y hy n hn => hX.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hX.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hX.2.2.2 y (hD y hy) h hh h' hh')
    (fun y hy n hn => hY.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hY.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hY.2.2.2 y (hD y hy) h hh h' hh')
    hp hgq hxe

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPairDone

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_identity : RDSPair :=
  rDSPair_of_cut spectral_pairing_inner_swap spectral_pairing_big_cell spectral_pairing_zero_right spectral_pairing_exhaustion spectral_pairing_orbital_membership spectral_pairing_operator
    spectral_pairing_locality

end Formalism.FourierDecayAlt.P.CutSE
end
end
