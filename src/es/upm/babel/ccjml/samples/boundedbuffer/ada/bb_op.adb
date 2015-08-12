--  bb.adb --  Implements a bounded buffer
--
--  Author : Manuel Carro

with Ada.Text_IO;
use Ada.Text_IO;

procedure Bb_Op is

   subtype Item_Type is Natural;

   Num_Consumers : constant Positive := 10;
   Num_Producers : constant Positive := 1;

   --  Constants and type definitions.  They cannot go into the object
   --  : only the state lives there!
   Buffer_Size : constant Natural := 10;

   --  A modular type gives a shorter and more readable code
   subtype Buffer_Quantity is Natural range 0 .. Buffer_Size;
   type Buffer_Range is mod Buffer_Size;

   --  The buffer itself in an array
   type Container_Array is array (Buffer_Range) of Item_Type;

   protected type Buffer is
      entry Get (Item : out Item_Type);  --  We need synchronization
      entry Put (Item : in Item_Type);
   private
      Container : Container_Array;
      Item_Counter : Buffer_Quantity := 0;
      Put_Pointer : Buffer_Range := Buffer_Range'First;
      Get_Pointer : Buffer_Range := Buffer_Range'First;
   end Buffer;

   protected body Buffer
   is
      entry Get
        (Item : out Item_Type)
      when Item_Counter > 0 is
      begin
         Item := Container (Get_Pointer);
         Get_Pointer := Get_Pointer + 1;
         Item_Counter := Item_Counter - 1;
      end Get;

      entry Put
        (Item : in Item_Type)
      when Item_Counter < Buffer_Size is
      begin
         Container (Put_Pointer) := Item;
         Put_Pointer := Put_Pointer + 1;
         Item_Counter := Item_Counter + 1;
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
         delay 2.0;
         Pool.Put (Item);
         Put_Line ("Task PUT item " & Item_Type'Image (Item));
         Item := Item_Type'Succ (Item);
      end loop;
   end Producer_Type;

   task type Consumer_Type;
   task body Consumer_Type is
      Item : Item_Type;
   begin
      loop
         Pool.Get (Item);
         Put_Line ("Task GOT item " & Item_Type'Image (Item));
      end loop;
   end Consumer_Type;

   --  Start a number of producers and consumers just by declarating them as
   --  components of an array.
   Consumers : array (1 .. Num_Consumers) of Consumer_Type;
   Producers : array (1 .. Num_Producers) of Producer_Type;

begin
   null;
end Bb_Op;
