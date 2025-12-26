/**CFile****************************************************************

  FileName    [AgdmapCommand.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Agdmap.]

  Synopsis    [External declarations.]

  Author      [Longfei Fan, Zhiyong Zhang, Chang Wu]

  Affiliation [Fudan University]

  Date        [August 1, 2023]

  Vision      [ 1.0 ]

***********************************************************************/

#include "base/main/main.h"
#include "agdmap.h"

ABC_NAMESPACE_IMPL_START

////////////////////////////////////////////////////////////////////////
///                      DECLARATIONS                                ///
////////////////////////////////////////////////////////////////////////
#ifndef ABC_NAMESPACE
extern "C"
{
  int Agdmap(Abc_Frame_t *pAbc, int argc, char **argv);
}
#endif

////////////////////////////////////////////////////////////////////////
///                      FUNCTION DEFINITIONS                        ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    [Main func for Agdmap - area command]

  Description []

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Agdmap(Abc_Frame_t *pAbc, int argc, char **argv)
{
  using namespace std;
  Abc_Ntk_t *pNtk, *pNtkRes;
  pNtk = Abc_FrameReadNtk(pAbc);

  auto run_mapper = [](bool delay, int k, int w, bool verbose, Abc_Ntk_t *ntk)
  {
    Abc_Ntk_t *res = nullptr;
    AgdMap::Para para(k, w, !delay, verbose);

    if ( ntk->pName != NULL )       // aviod undefined behavior
      std::cout << "\n" << ntk->pName << "\t is running ... \n";
    AgdMap::Mapper mapper(ntk, para);
    if (mapper.map() != 0)
      std::cout << "adgmap failed!\n";
    res = mapper.getNtk();
    return res;
  };

  int k = 6;
  int w = 8;
  bool delay_oriented = false;
  bool verbose = false;

  for (size_t i = 1; i < argc; ++i)
  {
    if (strcmp(argv[i], "-k") == 0)
    {
      k = atoi(argv[++i]);
      if (k < 3)
        goto usage;
    }
    else if (strcmp(argv[i], "-w") == 0)
    {
      w = atoi(argv[++i]);
      if (w < 3)
        w = 0;
    }
    else if (strcmp(argv[i], "-d") == 0)
      delay_oriented = true;
    else if (strcmp(argv[i], "-v") == 0)
      verbose = true;
    else if (strcmp(argv[i], "-h") == 0)
      goto usage;
    else
    {
      printf("unknown argument %s\n", argv[i]);
      goto usage;
    }
  }

  if (pNtk == NULL)
  {
    Abc_Print(-1, "Empty network.\n");
    return 0;
  }
  if (!Abc_NtkIsStrash(pNtk))
  {
    pNtk = Abc_NtkStrash(pNtk, 0, 0, 0);
    if (pNtk == NULL)
    {
      Abc_Print(-1, "Strashing before FPGA mapping has failed.\n");
      return 1;
    }
    pNtk = Abc_NtkBalance(pNtkRes = pNtk, 0, 0, 1);
    Abc_NtkDelete(pNtkRes);
    if (pNtk == NULL)
    {
      Abc_Print(-1, "Balancing before FPGA mapping has failed.\n");
      return 1;
    }
    if (!Abc_FrameReadFlag("silentmode"))
      Abc_Print(1, "The network was strashed and balanced before FPGA mapping.\n");
    // get the new network
    pNtkRes = run_mapper(delay_oriented, k, w, verbose, pNtk);
    if (pNtkRes == NULL)
    {
      Abc_NtkDelete(pNtk);
      Abc_Print(-1, "FPGA mapping has failed.\n");
      return 0;
    }
  }
  else
  {
    pNtkRes = run_mapper(delay_oriented, k, w, verbose, pNtk);
    if (pNtkRes == NULL)
    {
      Abc_Print(-1, "FPGA mapping has failed.\n");
      return 0;
    }
  }
  // replace the current network
  Abc_FrameReplaceCurrentNetwork(pAbc, pNtkRes);
  Abc_FrameClearVerifStatus(pAbc);

  return 0;

usage:
  Abc_Print(-2, "\nusage: agdmap\n");
  Abc_Print(-2, "\t         a patent pending FPGA technology mapping with adaptive gate decomposition algorithm \n");
  Abc_Print(-2, "\t-k  [int]   : LUT input size [default = 6]\n");
  Abc_Print(-2, "\t-w  [int]   : wide gate input size limit [default = 8]\n");
  Abc_Print(-2, "\t            : 0 means no gate decomposition\n");
  Abc_Print(-2, "\t-d          : delay-oriented technology mapping, default is area-oriented\n");
  Abc_Print(-2, "\t-v          : print verbose information\n");
  Abc_Print(-2, "\t-h          : print the command usage\n");
  return 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////

ABC_NAMESPACE_IMPL_END
