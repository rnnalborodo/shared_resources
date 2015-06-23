--  bb.adb --  Implements a one-item buffer with even/odd requests
--
--  Author : Manuel Carro

--  with Ada.Text_Io;
--  use Ada.Text_Io;

with Conc_IO;
use Conc_IO;

procedure Bb_Eo_Req is

   subtype Item_Type is Natural;

   Num_Consumers : constant Positive := 9;
   Num_Producers : constant Positive := 3;

   --  Constants and type definitions

   type Request_Type is (Even, Odd);

   protected type Buffer is
      --  Get can request an even item or an odd item at will.
      entry Get
        (Req : in     Request_Type;
         What : out Item_Type);
      --  Put can leave an even item or an odd item as dictated by the
      --  caller task.
      entry Put
        (What : in Item_Type);
   private
      Item : Item_Type;
      Item_Present : Boolean := False;
      entry Delayed_Get_Even
        (Req : in     Request_Type;
         What : out Item_Type);
      entry Delayed_Get_Odd
        (Req : in     Request_Type;
         What : out Item_Type);
   end Buffer;

   protected body Buffer
   is
      entry Get
        (Req : in     Request_Type;
         What : out Item_Type)
      when True is
      begin
         if Req = Even then
            requeue Delayed_Get_Even;
         else
            requeue Delayed_Get_Odd;
         end if;
      end Get;

      entry Delayed_Get_Even
        (Req : in     Request_Type;
         What : out Item_Type)
      when Item_Present and Item mod 2 = 0 is
      begin
         What := Item;
         Item_Present := False;
      end Delayed_Get_Even;

      entry Delayed_Get_Odd
        (Req : in     Request_Type;
         What : out Item_Type)
      when Item_Present and Item mod 2 = 1 is
      begin
         What := Item;
         Item_Present := False;
      end Delayed_Get_Odd;

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
   task body Producer_Type is
      Item : Item_Type := Item_Type'First;   --  Make every producer to produce
                                             --  different items
   begin
      loop
         delay 0.5;
         Pool.Put (Item);
         Put_Line ("Task PUT item " & Item_Type'Image (Item));
         Item := Item_Type'Succ (Item) mod 17;
      end loop;
   end Producer_Type;

   task type Consumer_Type (Which_Type : Request_Type);
   task body Consumer_Type is
      Item : Item_Type;
   begin
      loop
         Pool.Get (Which_Type, Item);
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
end Bb_Eo_Req;
