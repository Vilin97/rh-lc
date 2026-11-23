module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockRetr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjSecondFactor
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BaseAt
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CellRelIff
public import Mathlib.GroupTheory.Index
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjugatorMemUnipotent

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

theorem conjugator_mem_unipotent (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    g0 M δ hA L U hL hU ∈ UP p :=
  ⟨lOf_loUni M δ hA L U hL hU, ρOf_upUni M δ hA L U hL hU⟩

theorem H_le_UP (X : MP p) : KP M p ⊓ StabX p X ≤ UP p := fun h hh =>
  ⟨Formalism.L2.SG.Pf.ProdEP2Cut.loUni_of_int M hh.1.1, Formalism.L2.SG.Pf.ProdEP2Cut.upUni_of_int M hh.1.2⟩

theorem XP_eq (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    XP M δ u u' w L U = g0 M δ hA L U hL hU • Y0 M δ u u' w p := rfl

theorem mem_Ag_iff (x : GG p) : x ∈ Ag M δ u u' (p := p) w ↔ x ∈ StP M δ u u' w p ∧ x ∈ KP M p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h1⟩, h2, rfl⟩

end Formalism.L2.SG.Pf.CountAt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FixesBaseIff

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def tauU : UP p →* UP p where
  toFun x := ⟨tau p x, tau_mem_UP p x.2⟩
  map_one' := by ext1; exact (tau p).map_one
  map_mul' x y := by ext1; exact (tau p).map_mul x y

theorem tauU_tauU (x : UP p) : tauU p (tauU p x) = x := by
  ext1; exact tau_tau p x

def piU (πa : UP p →* UP p) : UP p →* UP p := (tauU p).comp (πa.comp (tauU p))

def piG (πa : UP p →* UP p) (x : GG p) : GG p :=
  if h : x ∈ UP p then ((piU p πa ⟨x, h⟩ : UP p) : GG p) else 1

theorem piG_of (πa : UP p →* UP p) (x : UP p) : piG p πa x = ((piU p πa x : UP p) : GG p) := by
  unfold piG; rw [dite_eq_left x.2]

theorem mem_StP_iff (x : GG p) :
    x ∈ StP M δ u u' w p ↔ x ∈ UP p ∧ x • Y0 M δ u u' w p = Y0 M δ u u' w p :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem fixes_base_iff (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (x : UP p) :
    (x : GG p) • Y0 M δ u u' w p = Y0 M δ u u' w p ↔ ((tauU p x : UP p) : GG p) • a.mat = a.mat := by
  rw [← (hB.choose_spec.2 (tauU p x))]
  constructor
  · intro h
    show tau p x • _ = _
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

theorem retr_of (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hD : CountAb.Data (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)
    (hB : BaseAt M δ u u' w p a) :
    Formalism.L2.SG.Pf.ProdEP2Core.Retr (StP M δ u u' w p) (UP p) (piG p πa) := by
  refine ⟨fun x hx => ((mem_StP_iff M δ u u' w p x).1 hx).1, fun x hx y hy => ?_, fun x hx => ?_, fun s hs => ?_⟩
  · have ex : piG p πa x = ((piU p πa ⟨x, hx⟩ : UP p) : GG p) := piG_of p πa ⟨x, hx⟩
    have ey : piG p πa y = ((piU p πa ⟨y, hy⟩ : UP p) : GG p) := piG_of p πa ⟨y, hy⟩
    have exy : piG p πa (x * y) = ((piU p πa (⟨x, hx⟩ * ⟨y, hy⟩) : UP p) : GG p) :=
      piG_of p πa (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [exy, ex, ey, map_mul]
    rfl
  · rw [show x = ((⟨x, hx⟩ : UP p) : GG p) from rfl, piG_of]
    refine (mem_StP_iff M δ u u' w p _).2 ⟨(piU p πa ⟨x, hx⟩).2, ?_⟩
    rw [fixes_base_iff M δ u u' w p a hB]
    have h1 : tauU p (piU p πa ⟨x, hx⟩) = πa (tauU p ⟨x, hx⟩) := by
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
    rw [h1]
    exact hD.mem _
  · obtain ⟨hsU, hsY⟩ := (mem_StP_iff M δ u u' w p s).1 hs
    rw [show s = ((⟨s, hsU⟩ : UP p) : GG p) from rfl, piG_of]
    have hfix : tauU p ⟨s, hsU⟩ ∈ MulAction.stabilizer (UP p) a.mat :=
      (fixes_base_iff M δ u u' w p a hB ⟨s, hsU⟩).1 hsY
    have h2 : piU p πa ⟨s, hsU⟩ = ⟨s, hsU⟩ := by
      simp only [piU, MonoidHom.comp_apply, hD.id _ hfix, tauU_tauU]
    rw [h2]

end Formalism.L2.SG.Pf.CountAt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauKPIff

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

theorem tauU_inj : Function.Injective (tauU p) := fun x y h => by
  rw [← tauU_tauU p x, ← tauU_tauU p y, h]

theorem tau_KP_iff (x : GG p) : tau p x ∈ KP M p ↔ x ∈ KP M p :=
  ⟨fun h => by have := tau_mem_KP M p h; rwa [tau_tau] at this, fun h => tau_mem_KP M p h⟩

section Parts

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a)

def gU : UP p := tauU p ⟨g0 M δ hA L U hL hU, conjugator_mem_unipotent M δ hA L U hL hU⟩ * hB.choose

theorem gU_smul : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
    phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' w L U) := by
  rw [XP_eq M δ u u' w hA L U hL hU, phi_smul p δ _ _ w (conjugator_mem_unipotent M δ hA L U hL hU), hB.choose_spec.1]
  show ((tau p (g0 M δ hA L U hL hU) * (hB.choose : GG p)) : GG p) • a.mat = _
  rw [mul_smul]

theorem mem_H_iff (x : UP p) :
    (x : GG p) ∈ KP M p ⊓ StabX p (XP M δ u u' w L U) ↔
      tauU p x ∈ CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB) := by
  show (x : GG p) ∈ KP M p ∧ (x : GG p) • XP M δ u u' (p := p) w L U = XP M δ u u' (p := p) w L U ↔
    tau p x ∈ KP M p ∧ (tauU p x : UP p) • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) =
      (gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat
  rw [tau_KP_iff]
  apply and_congr Iff.rfl
  have e : ∀ y : UP p, (y • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) : MP p) =
      (y : GG p) • (((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p)) := fun y => rfl
  have e2 : ((gU M δ u u' w hA L U hL hU a hB : UP p) • (a.mat : MP p) : MP p) =
      ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p) := rfl
  rw [e2, gU_smul]
  constructor
  · intro h
    show tau p (x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U)
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

end Parts

end Formalism.L2.SG.Pf.CountAt
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCells

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def cellEquiv (hD : Data W S N' K π) :
    Quotient (Setoid.ker (Formalism.L2.SG.Pf.ProdEP2Core.dcMap (Ak S K) (πk W S N' K π hD) (Hk W K g))) ≃
      Quotient (cellRel W N' K g) := by
  refine Equiv.ofBijective (Quotient.lift (fun k => (⟦toCell W S N' K π g hD k⟧ : Quotient (cellRel W N' K g)))
    (fun k₁ k₂ h => ?_)) ⟨?_, ?_⟩
  · apply Quotient.sound
    exact (cellRel_iff W S N' K π g hD k₁ k₂).2
      ((Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).1 h)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h k₁ =>
      induction y using Quotient.inductionOn with
      | h k₂ =>
        apply Quotient.sound
        have h2 := Quotient.exact hxy
        exact (Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).2
          ((cellRel_iff W S N' K π g hD k₁ k₂).1 h2)
  · intro y
    induction y using Quotient.inductionOn with
    | h c =>
      obtain ⟨k, rfl⟩ := toCell_surj W S N' K π g hD c
      exact ⟨⟦k⟧, rfl⟩

theorem card_cells (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hk W K g).map (πk W S N' K π hD)).index := by
  rw [← Nat.card_congr (cellEquiv W S N' K π g hD)]
  exact Formalism.L2.SG.Pf.ProdEP2Core.card_dc (Ak S K) (πk W S N' K π hD) (Hk W K g) (πk_id W S N' K π hD)

end Formalism.L2.SG.Pf.CountAb
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IndexEqRelIndex

section

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

theorem index_eq_relIndex (hD : Data W S N' K π) :
    ((Hk W K g).map (πk W S N' K π hD)).index = ((Hs W K g).map π).relIndex (K ⊓ S) := by
  let e : ↥(K ⊓ S) →* ↥(Ak S K) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simp only [Ak, Subgroup.mem_subgroupOf]; exact x.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Surjective e := fun a =>
    ⟨⟨a.1.1, a.1.2, by have h := a.2; simp only [Ak, Subgroup.mem_subgroupOf] at h; exact h⟩, rfl⟩
  rw [← Subgroup.index_comap_of_surjective _ he]
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k.1, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hk
    · have h2 := congrArg (fun y : ↥(Ak S K) => ((y : ↥K) : G)) hkx
      simpa [πk, e] using h2
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hy
    · apply Subtype.ext
      apply Subtype.ext
      simpa [πk, e] using hyx

theorem card_cells' (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hs W K g).map π).relIndex (K ⊓ S) := (card_cells W S N' K π g hD).trans (index_eq_relIndex W S N' K π g hD)

end Formalism.L2.SG.Pf.CountAb
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountAtOfParts

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

section Parts2

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (πa : UP p →* UP p)
  (hD : CountAb.Data a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)

theorem img_eq :
    img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U)) (H_le_UP M _) =
      (((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).map (tauU p)).map (UP p).subtype := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hU' := H_le_UP M _ hh
    have hy := (mem_H_iff M δ u u' w hA L U hL hU a hB ⟨h, hU'⟩).1 hh
    refine ⟨tauU p (πa (tauU p ⟨h, hU'⟩)), ⟨πa (tauU p ⟨h, hU'⟩), ⟨_, hy, rfl⟩, rfl⟩, ?_⟩
    exact (piG_of p πa ⟨h, hU'⟩).symm
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨((tauU p y : UP p) : GG p), ?_, ?_⟩
    · exact (mem_H_iff M δ u u' w hA L U hL hU a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hy)
    · show piG p πa ((tauU p y : UP p) : GG p) = _
      rw [piG_of]
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
      rfl

include hB in
theorem Ag_eq :
    Ag M δ u u' (p := p) w =
      (((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat).map (tauU p)).map (UP p).subtype := by
  ext z
  rw [mem_Ag_iff]
  constructor
  · rintro ⟨hS, hK⟩
    obtain ⟨hzU, hzY⟩ := (mem_StP_iff M δ u u' w p z).1 hS
    have hfix := (fixes_base_iff M δ u u' w p a hB ⟨z, hzU⟩).1 hzY
    refine ⟨⟨z, hzU⟩, ⟨tauU p ⟨z, hzU⟩, ⟨?_, ?_⟩, tauU_tauU p _⟩, rfl⟩
    · show ((tauU p ⟨z, hzU⟩ : UP p) : GG p) ∈ KP M p
      exact tau_mem_KP M p hK
    · exact hfix
  · rintro ⟨_, ⟨y, ⟨hyK, hyS⟩, rfl⟩, rfl⟩
    refine ⟨(mem_StP_iff M δ u u' w p _).2 ⟨(tauU p y).2, ?_⟩, ?_⟩
    · exact (fixes_base_iff M δ u u' w p a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hyS)
    · exact tau_mem_KP M p hyK


include hD in
theorem countAt_of_parts (v : ℝ)
    (hv : (Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) : ℝ) = v)
    (hpos : Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) ≠ 0) :
    CountAt M δ u u' w hA L U hL hU v := by
  have hcard := CountAb.card_cells' (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
    (gU M δ u u' w hA L U hL hU a hB) hD
  have hidx : (img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U))
      (H_le_UP M _)).relIndex (Ag M δ u u' (p := p) w) =
      ((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).relIndex
        ((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat) := by
    rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB,
      Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
      Subgroup.relIndex_map_map_of_injective _ _ (tauU_inj (p := p))]
  refine ⟨UP p, piG p πa, retr_of M δ u u' w p a πa hD hB, H_le_UP M _, conjugator_mem_unipotent M δ hA L U hL hU, ?_, ?_, ?_⟩
  · rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB]
    apply Subgroup.map_mono
    apply Subgroup.map_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hD.kπ z hz.1, hD.mem z⟩
  · rw [hidx, ← hcard]
    exact hpos
  · rw [hidx, ← hcard, hv]

end Parts2

end Formalism.L2.SG.Pf.CountAt
end
end
end
