module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CwOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EtaleCohomologyNegativeVanishingDegreeZero

@[expose] public section

namespace PositivityTheory.CWB

open PositivityTheory.CW

theorem casselmanWallach : GlobalTheory.Published.CasselmanWallach := cw_of maxPr

end PositivityTheory.CWB
