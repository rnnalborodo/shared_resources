--  bb.adb --  Implements a one-item buffer with even/odd requests
--
--  Author : Manuel Carro

--  with Ada.Text_Io;
--  use Ada.Text_Io;

with Conc_IO;
use Conc_IO;

procedure Bb_Eo_Entfam is

   subtype Item_Type is Natural;

   Num_Consumers : constant Positive := 9;
   Num_Producers : constant Positive := 3;

   --  Constants and type definitions

   type Request_Type is (Even, Odd);

   protected type Buffer is
      entry Get (Request_Type)(What : out Item_Type);
      entry Put (What : in Item_Type);
   private
      Item : Item_Type;
      Item_Present : Boolean := False;
   end Buffer;

   protected body Buffer
   is
      entry Get (for I in Request_Type)
        (What : out Item_Type)
      when Item_Present and ((I = Even) = (Item mod 2 = 0)) is
      begin
         What := Item;
         Item_Present := False;
      end Get;

      entry Put
        (What : in Item_Type)
      when not Item_Present is
      begin
         Item := What;
         Item_Present := True;
      end Put;
   end Buffer;

   Pool : Buffer;

   --  Each producer and consumer is a task
   task type Producer_Type;
   task body Producer_Type is      --  Make every producer produce
      Item : Item_Type := Item_Type'First; --  different items
   begin
      loop
         delay 0.5;
         Pool.Put (Item);
         Put_Line ("Task PUT item " & Item_Type'Image (Item));
         Item := Item_Type'Succ (Item) mod 18;
      end loop;
   end Producer_Type;

   task type Consumer_Type (Which_Type : Request_Type);
   task body Consumer_Type is
      Item : Item_Type;
   begin
      Put_Line ("I want "&
                Request_Type'Image (Which_Type) &
                " data");
      loop
         Pool.Get (Which_Type)(Item);
         Put_Line ("Task GOT item " & Item_Type'Image (Item));
      end loop;
   end Consumer_Type;

   --  Start a number of producers and consumers just by declarating them as
   --  components of an array.
   Consumers_Even : array (1 .. Num_Consumers / 2) of Consumer_Type (Even);
   Consumers_Odd : array (1 .. Num_Consumers / 2) of Consumer_Type (Odd);
   Producers : array (1 .. Num_Producers) of Producer_Type;

begin
   null;
end Bb_Eo_Entfam;
