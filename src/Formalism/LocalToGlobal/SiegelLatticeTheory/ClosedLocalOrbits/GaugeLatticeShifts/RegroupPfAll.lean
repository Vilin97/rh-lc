module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfColCover
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabFlag
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCarAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDensePf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfNSA

section

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions

section NSAPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NDense : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

theorem nStrongApproxC_of (hD : NDense) : NStrongApproxC := by
  intro D X u hK hKL n hn c
  have hcl := Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL
  have hc : Continuous fun m : X.B.I.Gf => c⁻¹ * (m⁻¹ * n) * c :=
    (continuous_const.mul (continuous_inv.mul continuous_const)).mul continuous_const
  obtain ⟨ν, hνr, hν1, hν2, hνU⟩ := hD D X u n hn {m | c⁻¹ * (m⁻¹ * n) * c ∈ X.K2} (hcl.2.preimage hc)
    (by simpa using hK.1)
  exact ⟨ν, hνr, hν1, hν2, hνU⟩

end NSAPf

end Formalism.L2.SG.Pf.RegroupPf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfOrbitAlgOut

section

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem orbit_algebra_of_stabilizer (hC : TermCarC) (hS : StabNC) : OrbitAlgC :=
  orbitAlgC_of Formalism.L2.SG.Pf.nilradical_conj_level' hC hS

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabNFinal

section

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions Formalism.L2.SG.Full

theorem stabilizer_of_neat_level
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabNC :=
  stabNC_of lattice_stabilizer_holds flag_stabilizer_holds (orthogonal_stabilizer_of_neat hN)

end Formalism.L2.SG.Pf.RegroupPf
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfAll

section

@[expose] public section

namespace Formalism.L2.SG.Pf.RegroupPf

theorem foldReadyX_K2Level : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), X.LevelSubgroupNormalized →
    Formalism.L2.SG.PoincareInHH.Cut.FoldReadyX X :=
  fun _ X _ => Formalism.L2.SG.PoincareInHH.Cut.foldReadyX_holds X

theorem neatKu_K2Level : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X)
    (u : D.what₂.Word), X.LevelSubgroupNormalized → Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK :=
  fun _ X Y u _ => Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X u Y.hK
    (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u Y.hK)

theorem nDense_RG : NDense := Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation

theorem slabCoverC_holds : Formalism.L2.SG.Pf.Slab.SlabCoverC := Formalism.L2.SG.Pf.SlabCoverPf.slab_covering_of_strong_approx nDense_RG Formalism.L2.SG.Pf.nilradical_conj_level'
  (fun _ X u => Formalism.L2.SG.Pf.Level.ratLevi_holds X u) (fun _ X => Formalism.L2.SG.Pf.psiDd_holds X)

theorem regroupC_all : Formalism.L2.SG.Pf.Slab.RegroupC := regrouping_of_neatness (nStrongApproxC_of nDense_RG)
  (orbit_algebra_of_stabilizer term_carrier_holds (stabilizer_of_neat_level neatKu_K2Level)) slabCoverC_holds foldReadyX_K2Level neatKu_K2Level

end Formalism.L2.SG.Pf.RegroupPf
end
end
