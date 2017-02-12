--------------------------------------------------------------------------------
-- Compiler for the STG Language                                              --
-- By Michael B. Gale (michael.gale@cl.cam.ac.uk)                             --
--------------------------------------------------------------------------------

module CmdArgs (
    CmdArgs(..),

    parseCmdArgs
) where

--------------------------------------------------------------------------------

import Options.Applicative

--------------------------------------------------------------------------------

data CmdArgs = MkCmdArgs {
    argsInputs :: [FilePath],
    argsEntry  :: String,
    argsQuiet  :: Bool
}

cmdArgsP :: Parser CmdArgs
cmdArgsP = MkCmdArgs
    <$> many (argument str (metavar "FILES..."))
    <*> strOption (long "entry"      <>
                   short 'e'         <>
                   metavar "BINDING" <>
                   value "main"      <>
                   help "Name of the program's entry point")
    <*> switch (long "no-stdin" <>
                help "Tells the compiler that no stdin is available/usable.")

cmdArgsOpts :: ParserInfo CmdArgs
cmdArgsOpts = info (helper <*> cmdArgsP) fullDesc

-- | Parses command line arguments.
parseCmdArgs :: IO CmdArgs
parseCmdArgs = execParser cmdArgsOpts
