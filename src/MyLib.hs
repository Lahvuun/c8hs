module MyLib (run) where

import qualified System.Random as R
import Control.Concurrent (threadDelay)
import Data.Bits (Bits (shiftL, shiftR, xor, (.&.)))
import qualified Data.ByteString.Builder as BSB
import qualified Data.ByteString.Lazy as BS
import Data.ShortWord (Word4)
import qualified Data.Vector.Unboxed as V
import Data.Word (Word16, Word8)
import Numeric (showHex)
import qualified SDL

newtype InitializationError = InitializationError String

newtype ExecutionError = ExecutionError String

data VM = VM
  { vmInstructionPointer :: Word16,
    vmStack :: [Word16],
    vmRegisters :: V.Vector Word8,
    vmAddressRegister :: Word16,
    vmDelayTimer :: Word8,
    vmSoundTimer :: Word8,
    vmMemory :: V.Vector Word8,
    vmRNG :: R.StdGen,
    vmScreen :: V.Vector Bool
  }

getDefaultScreenWidth :: Integral a => a
getDefaultScreenWidth = 64

getDefaultScreenHeight :: Integral a => a
getDefaultScreenHeight = 32

getTotalMemorySize :: Integral a => a
getTotalMemorySize = 4096

getDefaultInterpreterAreaSize :: Integral a => a
getDefaultInterpreterAreaSize = 512

getDefaultReservedAreaSize :: Integral a => a
getDefaultReservedAreaSize = 352

getProgramAreaSize :: Integral a => a
getProgramAreaSize = getTotalMemorySize - getDefaultInterpreterAreaSize - getDefaultReservedAreaSize

getFont :: V.Vector Word8
getFont =
  V.fromList $
    mconcat
      [ [0xf0, 0x90, 0x90, 0x90, 0xf0],
        [0x20, 0x60, 0x20, 0x20, 0x70],
        [0xf0, 0x10, 0xf0, 0x80, 0xf0],
        [0xf0, 0x10, 0xf0, 0x10, 0xf0],
        [0x90, 0x90, 0xf0, 0x10, 0x10],
        [0xf0, 0x80, 0xf0, 0x10, 0xf0],
        [0xf0, 0x80, 0xf0, 0x90, 0xf0],
        [0xf0, 0x10, 0x20, 0x40, 0x40],
        [0xf0, 0x90, 0xf0, 0x90, 0xf0],
        [0xf0, 0x90, 0xf0, 0x10, 0xf0],
        [0xf0, 0x90, 0xf0, 0x90, 0x90],
        [0xe0, 0x90, 0xe0, 0x90, 0xe0],
        [0xf0, 0x80, 0x80, 0x80, 0xf0],
        [0xe0, 0x90, 0x90, 0x90, 0xe0],
        [0xf0, 0x80, 0xf0, 0x80, 0xf0],
        [0xf0, 0x80, 0xf0, 0x80, 0x80]
      ]

createVM :: BS.ByteString -> R.StdGen -> Either InitializationError VM
createVM program rng = initializeVM rng <$> initializeMemory program

initializeVM :: R.StdGen -> V.Vector Word8 -> VM
initializeVM rng memory =
  VM
    { vmInstructionPointer = getDefaultInterpreterAreaSize,
      vmStack = [],
      vmRegisters = V.replicate 16 0,
      vmAddressRegister = 0,
      vmDelayTimer = 0,
      vmSoundTimer = 0,
      vmMemory = memory,
      vmRNG = rng,
      vmScreen = V.replicate (getDefaultScreenWidth * getDefaultScreenHeight) False
    }

initializeMemory :: BS.ByteString -> Either InitializationError (V.Vector Word8)
initializeMemory program
  | getDefaultInterpreterAreaSize < fontLength = Left $ InitializationError "interpreter area too small to fit font"
  | getProgramAreaSize < programLength = Left $ InitializationError "program area too small to fit rom"
  | otherwise = Right $ interpreterArea <> programArea <> reservedArea
  where
    fontLength = V.length getFont
    programBytes = V.fromList $ BS.unpack program
    programLength = V.length programBytes
    interpreterArea = getFont <> V.replicate (getDefaultInterpreterAreaSize - fontLength) 0
    programArea = programBytes <> V.replicate (getProgramAreaSize - programLength) 0
    reservedArea = V.replicate getDefaultReservedAreaSize 0

splitNibbles :: Word8 -> (Word8, Word8)
splitNibbles x = (fromInteger (toInteger (x `shiftR` 4)), fromInteger (toInteger (x .&. 0xf)))

readByteFromMemory :: V.Vector Word8 -> Word16 -> Word8
readByteFromMemory bytes index = bytes V.! fromEnum index

readCurrentInstruction :: VM -> (Word8, Word8, Word8, Word8)
readCurrentInstruction vm = (a, b, c, d)
  where
    (a, b) = splitNibbles $ readByteFromMemory (vmMemory vm) (vmInstructionPointer vm)
    (c, d) = splitNibbles $ readByteFromMemory (vmMemory vm) (vmInstructionPointer vm + 1)

executeInstruction :: (Word8, Word8, Word8, Word8) -> VM -> Either ExecutionError VM
executeInstruction instruction vm = case instruction of
  (0x0, 0x0, 0xe, 0x0) -> Right $ advanceIP $ vm {vmScreen = V.replicate (getDefaultScreenWidth * getDefaultScreenHeight) False}
  (0x0, 0x0, 0xe, 0xe) -> Right $ vm {vmInstructionPointer = head (vmStack vm), vmStack = tail (vmStack vm)}
  (0x1, a, b, c) -> Right $ vm {vmInstructionPointer = decodeAddress (a, b, c)}
  (0x2, a, b, c) -> Right $ vm {vmInstructionPointer = decodeAddress (a, b, c), vmStack = (vmInstructionPointer vm + 2) : vmStack vm}
  (0x3, a, b, c) -> Right $ (advanceIP . (if readRegister a vm == decodeByte (b, c) then advanceIP else id)) vm
  (0x4, a, b, c) -> Right $ (advanceIP . (if readRegister a vm /= decodeByte (b, c) then advanceIP else id)) vm
  (0x6, a, b, c) -> Right $ advanceIP $ updateRegister a (decodeByte (b, c)) vm
  (0x7, a, b, c) -> Right $ advanceIP $ updateRegister a (decodeByte (b, c) + readRegister a vm) vm
  (0x8, a, b, 0x0) -> Right $ advanceIP $ updateRegister a (readRegister b vm) vm
  (0x8, a, b, 0x2) -> Right $ advanceIP $ updateRegister a (readRegister a vm .&. readRegister b vm) vm
  (0x8, a, b, 0x4) -> Right $ advanceIP $ let vx = readRegister a vm
                                              vy = readRegister b vm
                                          in updateRegister 0xf (if vy > 255 - vx then 1 else 0) (updateRegister a (vx + vy) vm)
  (0x8, a, b, 0x5) -> Right $ advanceIP $ let vx = readRegister a vm
                                              vy = readRegister b vm
                                          in updateRegister 0xf (if vy > vx then 1 else 0) (updateRegister a (vx - vy) vm)
  (0x9, a, b, 0x0) -> Right $ (advanceIP . (if readRegister a vm /= readRegister b vm then advanceIP else id)) vm
  (0xa, a, b, c) -> Right $ advanceIP $ vm {vmAddressRegister = decodeAddress (a, b, c)}
  (0xc, a, b, c) -> Right $ advanceIP $ let (number, rng) = R.genWord8 (vmRNG vm)
                                        in updateRegister a (number .&. decodeByte (b, c)) vm {vmRNG = rng}
  (0xd, a, b, c) -> Right $ advanceIP $ let (newScreen, newVFValue) = drawSprite (readRegister a vm) (readRegister b vm) (V.toList (V.slice (fromEnum (vmAddressRegister vm)) (fromEnum c) (vmMemory vm))) (vmScreen vm)
                                        in updateRegister 0xf newVFValue vm {vmScreen = newScreen}
  -- TODO: handle keypresses.
  (0xe, a, 0x9, 0xe) -> Right $ advanceIP vm
  (0xe, a, 0xa, 0x1) -> Right $ (advanceIP . advanceIP) vm
  (0xf, a, 0x0, 0x7) -> Right $ advanceIP $ updateRegister a (vmDelayTimer vm) vm
  (0xf, a, 0x1, 0x5) -> Right $ advanceIP $ vm {vmDelayTimer = readRegister a vm}
  (0xf, a, 0x1, 0x8) -> Right $ advanceIP $ vm {vmSoundTimer = readRegister a vm}
  (0xf, a, 0x1, 0xe) -> Right $ advanceIP $ vm {vmAddressRegister = fromInteger (toInteger (vmAddressRegister vm) + toInteger (readRegister a vm))}
  (0xf, a, 0x2, 0x9) -> Right $ advanceIP $ vm {vmAddressRegister = fromInteger (toInteger (readRegister a vm * 5))}
  (0xf, a, 0x3, 0x3) -> Right $ advanceIP $ let value = readRegister a vm
                                                position = fromEnum (vmAddressRegister vm)
                                            in vm {vmMemory = vmMemory vm V.// [(position, (value `div` 100) `rem` 10), (position + 1, (value `div` 10) `rem` 10), (position + 2, value `rem` 10)]}
  (0xf, a, 0x6, 0x5) -> Right $ advanceIP $ vm {vmRegisters = V.slice (fromEnum (vmAddressRegister vm)) (fromEnum a + 1) (vmMemory vm) <> V.drop (fromEnum a) (vmRegisters vm), vmAddressRegister = fromInteger (toInteger (vmAddressRegister vm) + toInteger a + 1)}
  (a, b, c, d) -> Left $ ExecutionError $ "unknown instruction: " ++ mconcat (fmap (`showHex` "") [a, b, c, d])

advanceIP :: VM -> VM
advanceIP vm = vm {vmInstructionPointer = vmInstructionPointer vm + 2}

decodeByte :: (Word8, Word8) -> Word8
decodeByte (a, b) = a `shiftL` 4 + b

decodeAddress :: (Word8, Word8, Word8) -> Word16
decodeAddress (a, b, c) = fromInteger $ toInteger a `shiftL` 8 + toInteger b `shiftL` 4 + toInteger c

updateRegister :: Word8 -> Word8 -> VM -> VM
updateRegister x n vm = vm {vmRegisters = vmRegisters vm V.// [(fromEnum x, n)]}

readRegister :: Word8 -> VM -> Word8
readRegister x vm = vmRegisters vm V.! fromEnum x

drawSprite :: Word8 -> Word8 -> [Word8] -> V.Vector Bool -> (V.Vector Bool, Word8)
drawSprite x y sprite pixels = (pixels V.// replacementPixels, if pixelsWereUnset then 1 else 0)
  where
    ix = fromEnum x
    iy = fromEnum y
    spritePixels = [(ix + bx + (iy + by) * getDefaultScreenWidth, b) | (bx, by, b) <- spriteBytesToBooles 0 sprite, ix + bx < getDefaultScreenWidth, iy + by < getDefaultScreenHeight]
    originalPixels = [(i, pixels V.! i) | (i, _) <- spritePixels]
    replacementPixels = (\((si, sv), (_, ov)) -> (si, sv `xor` ov)) <$> zip spritePixels originalPixels
    pixelsWereUnset = or $ (\((_, sv), (_, ov)) -> sv && ov) <$> zip spritePixels originalPixels

spriteByteToBool :: Int -> Word8 -> [(Int, Int, Bool)]
spriteByteToBool height x = [(n, height, x .&. b > 0) | (b, n) <- zip [0x80, 0x40, 0x20, 0x10, 0x8, 0x4, 0x2, 0x1] [0 .. 7]]

spriteBytesToBooles :: Int -> [Word8] -> [(Int, Int, Bool)]
spriteBytesToBooles _ [] = []
spriteBytesToBooles height (x : xs) = spriteByteToBool height x ++ spriteBytesToBooles (height + 1) xs

reduceTimer :: Word8 -> Word8 -> Word8
reduceTimer timerValue delta = if delta > timerValue then 0 else timerValue - delta

updateTimers :: Word8 -> VM -> VM
updateTimers delta vm = vm {vmDelayTimer = delayTimer, vmSoundTimer = soundTimer}
  where
    delayTimer = reduceTimer (vmDelayTimer vm) delta
    soundTimer = reduceTimer (vmSoundTimer vm) delta

putScreen :: [Bool] -> IO ()
putScreen [] = putStrLn ""
putScreen pixels = putStrLn (mconcat $ fmap (\b -> if b then "o" else ".") left) >> putScreen right
  where
    (left, right) = splitAt getDefaultScreenWidth pixels

formatCurrentInstruction :: (Word8, Word8, Word8, Word8) -> String
formatCurrentInstruction (a, b, c, d) = mconcat $ fmap (`showHex` "") [a, b, c, d]

runVM :: VM -> IO ()
runVM vm = do
  threadDelay 16666
  putScreen $ V.toList $ vmScreen vm
  putStrLn $ "current instruction is: " ++ formatCurrentInstruction (readCurrentInstruction vm)
  putStrLn $ "current instruction pointer is: " ++ vmInstructionPointer vm `showHex` ""
  case executeInstruction (readCurrentInstruction vm) (updateTimers 1 vm) of
    Left (ExecutionError message) -> putStrLn message
    Right vm -> runVM vm

run :: BS.ByteString -> IO ()
run program = do
  rng <- R.initStdGen
  case createVM program rng of
    Left (InitializationError message) -> putStrLn message
    Right vm -> runVM vm

-- SDL.initialize [SDL.InitVideo, SDL.InitEvents]
-- SDL.quit
